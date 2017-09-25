/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.java_smt.solvers.smtinterpol;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ImmutableSet.Builder;
import com.google.common.collect.Lists;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import javax.annotation.Nullable;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractModel.CachingAbstractModel;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

class SmtInterpolModel extends CachingAbstractModel<Term, Sort, SmtInterpolEnvironment> {

  /**
   * Iteration over UF-model needs variables for parameters. These variables will never be used
   * anywhere else. Let's hope to never get a colliding symbol from a user :-)
   */
  private static final String FRESH_VAR = "@__javasmt_internal_param_for_UF__@";

  private final Model model;
  private final SmtInterpolFormulaCreator formulaCreator;

  SmtInterpolModel(Model pModel, FormulaCreator<Term, Sort, SmtInterpolEnvironment, ?> pCreator) {
    super(pCreator);
    formulaCreator = (SmtInterpolFormulaCreator) pCreator;
    model = pModel;
  }

  @Nullable
  @Override
  public Object evaluateImpl(Term f) {
    Term out = model.evaluate(f);
    return getValue(out);
  }

  @Override
  protected ImmutableList<ValueAssignment> modelToList() {
    Builder<ValueAssignment> assignments = ImmutableSet.builder();

    for (FunctionSymbol symbol : model.getDefinedFunctions()) {
      final String name = symbol.getApplicationString();
      if (symbol.getParameterSorts().length == 0) { // simple variable or array
        Term variable = creator.getEnv().term(name);
        if (symbol.getReturnSort().isArraySort()) {
          assignments.addAll(getArrayAssignment(name, variable, variable, Collections.emptyList()));
        } else {
          assignments.add(
              new ValueAssignment(
                  creator.encapsulateWithTypeOf(variable),
                  name,
                  getValue(model.getFunctionDefinition(name, new TermVariable[] {})),
                  Collections.emptySet()));
        }
      } else { // uninterpreted function
        assignments.addAll(getUFAssignment(symbol));
      }
    }

    return assignments.build().asList();
  }

  private Collection<ValueAssignment> getUFAssignment(FunctionSymbol symbol) {
    final Collection<ValueAssignment> assignments = new ArrayList<>();
    final String name = symbol.getApplicationString();

    // use fresh variables as utility parameters
    TermVariable[] args = new TermVariable[symbol.getParameterSorts().length];
    for (int i = 0; i < args.length; i++) {
      args[i] = creator.getEnv().variable(FRESH_VAR + i, symbol.getParameterSorts()[i]);
    }

    // get ITE-structure and split it into its values
    Term value = model.getFunctionDefinition(name, args);
    while (value instanceof ApplicationTerm) {
      ApplicationTerm app = (ApplicationTerm) value;
      if ("ite".equals(app.getFunction().getApplicationString())) {
        Term cond = app.getParameters()[0];
        Term ifCase = app.getParameters()[1];
        Term thenCase = app.getParameters()[2];
        assignments.add(getAssignment(name, args, cond, ifCase));

        value = thenCase; // recursive unrolling of the ITE-structure
      }
    }

    return assignments;
  }

  private ValueAssignment getAssignment(String name, TermVariable[] args, Term cond, Term ifCase) {
    Term[] arguments = new Term[args.length];
    // we expect one part for each parameter: "and (= @p0 123) (= @p1 123) (= @p2 123)"
    for (Term part : splitConjunction((ApplicationTerm) cond)) {
      // each part looks like "= @p0 123"
      Term[] params = ((ApplicationTerm) part).getParameters();
      int index = Integer.parseInt(params[0].toString().substring(FRESH_VAR.length()));
      arguments[index] = params[1];
    }

    List<Object> argumentInterpretation = new ArrayList<>();
    for (Term param : arguments) {
      argumentInterpretation.add(getValue(param));
    }

    return new ValueAssignment(
        creator.encapsulateWithTypeOf(creator.getEnv().term(name, arguments)),
        name,
        getValue(ifCase),
        argumentInterpretation);
  }

  private Collection<Term> splitConjunction(ApplicationTerm cond) {
    if ("and".equals(cond.getFunction().getApplicationString())) {
      return Lists.newArrayList(cond.getParameters());
    } else {
      return Collections.singleton(cond);
    }
  }

  private Collection<ValueAssignment> getArrayAssignment(
      String symbol, Term key, Term array, List<Object> upperIndices) {
    assert array.getSort().isArraySort();
    Collection<ValueAssignment> assignments = new ArrayList<>();
    Term evaluation = model.evaluate(array);

    // get all assignments for the current array
    while (evaluation instanceof ApplicationTerm) {
      ApplicationTerm arrayEval = (ApplicationTerm) evaluation;
      FunctionSymbol funcDecl = arrayEval.getFunction();
      Term[] params = arrayEval.getParameters();
      if (funcDecl.isIntern() && "store".equals(funcDecl.getName())) {
        Term index = params[1];
        Term content = params[2];

        List<Object> innerIndices = Lists.newArrayList(upperIndices);
        innerIndices.add(evaluateImpl(index));

        Term select = creator.getEnv().term("select", key, index);
        if (content.getSort().isArraySort()) {
          assignments.addAll(getArrayAssignment(symbol, select, content, innerIndices));
        } else {
          assignments.add(
              new ValueAssignment(
                  creator.encapsulateWithTypeOf(select),
                  symbol,
                  evaluateImpl(content),
                  innerIndices));
        }

        evaluation = params[0]; // unwrap recursive for more values
      } else {
        // we found the basis of the array
        break;
      }
    }

    return assignments;
  }

  @Override
  public String toString() {
    return model.toString();
  }

  private Object getValue(Term value) {
    FormulaType<?> type = creator.getFormulaType(value);
    if (type.isBooleanType()) {
      return value.getTheory().mTrue == value;
    } else if (value instanceof ConstantTerm
        && ((ConstantTerm) value).getValue() instanceof Rational) {

      /*
       * From SmtInterpol documentation (see {@link ConstantTerm#getValue}),
       * the output is SmtInterpol's Rational unless it is a bitvector,
       * and currently we do not support bitvectors for SmtInterpol.
       */
      Rational rationalValue = (Rational) ((ConstantTerm) value).getValue();
      org.sosy_lab.common.rationals.Rational out =
          org.sosy_lab.common.rationals.Rational.of(
              rationalValue.numerator(), rationalValue.denominator());
      if (formulaCreator.getFormulaTypeOfSort(value.getSort()).isIntegerType()) {
        assert out.isIntegral();
        return out.getNum();
      } else {
        return out;
      }
    } else {

      throw new IllegalArgumentException("Unexpected value: " + value);
    }
  }

  @Override
  public void close() {}
}
