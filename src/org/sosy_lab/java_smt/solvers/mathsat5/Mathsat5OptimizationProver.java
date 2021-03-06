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

package org.sosy_lab.java_smt.solvers.mathsat5;

import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5FormulaManager.getMsatTerm;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_OPTIMUM;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_assert_formula;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_check_sat;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_create_objective_iterator;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_destroy_objective_iterator;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_objective_iterator_has_next;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_objective_iterator_next;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_objective_value_is_unbounded;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_objective_value_repr;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_pop_backtrack_point;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_push_backtrack_point;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_push_maximize;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_push_minimize;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_set_model;

import com.google.common.collect.ImmutableMap;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import javax.annotation.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

class Mathsat5OptimizationProver extends Mathsat5AbstractProver<Void>
    implements OptimizationProverEnvironment {
  private final UniqueIdGenerator idGenerator = new UniqueIdGenerator();

  /** Number of the objective -> objective pointer. */
  private @Nullable List<Long> objectives = null;

  /**
   * ID given to user -> number of the objective. Size corresponds to the number of currently
   * existing objectives.
   */
  private Map<Integer, Integer> objectiveMap;

  /** Stack of the objective maps. Some duplication, but shouldn't be too important. */
  private final Deque<ImmutableMap<Integer, Integer>> stack;

  Mathsat5OptimizationProver(
      Mathsat5SolverContext pMgr,
      ShutdownNotifier pShutdownNotifier,
      Mathsat5FormulaCreator creator,
      Set<ProverOptions> options) {
    super(pMgr, options, creator, pShutdownNotifier);
    objectiveMap = new HashMap<>();
    stack = new ArrayDeque<>();
  }

  @Override
  protected void createConfig(Map<String, String> pConfig) {
    pConfig.put("model_generation", "true");
  }

  @Override
  @Nullable
  public Void addConstraint(BooleanFormula constraint) {
    msat_assert_formula(curEnv, getMsatTerm(constraint));
    return null;
  }

  @Override
  public int maximize(Formula objective) {
    // todo: code duplication.
    int id = idGenerator.getFreshId();
    objectiveMap.put(id, objectiveMap.size());
    msat_push_maximize(curEnv, getMsatTerm(objective), null, null);
    return id;
  }

  @Override
  public int minimize(Formula objective) {
    int id = idGenerator.getFreshId();
    objectiveMap.put(id, objectiveMap.size());
    msat_push_minimize(curEnv, getMsatTerm(objective), null, null);
    return id;
  }

  @Override
  public OptStatus check() throws InterruptedException, SolverException {
    boolean out = msat_check_sat(curEnv);
    if (out) {
      if (!objectiveMap.isEmpty()) {
        objectives = new ArrayList<>();
        long it = msat_create_objective_iterator(curEnv);
        while (msat_objective_iterator_has_next(it) != 0) {
          long[] objectivePtr = new long[1];
          int status = msat_objective_iterator_next(it, objectivePtr);
          assert status == 0;
          objectives.add(objectivePtr[0]);
        }
        msat_destroy_objective_iterator(it);
      }
      return OptStatus.OPT;
    } else {
      return OptStatus.UNSAT;
    }
  }

  @Override
  public void push() {
    msat_push_backtrack_point(curEnv);
    stack.add(ImmutableMap.copyOf(objectiveMap));
  }

  @Override
  public void pop() {
    msat_pop_backtrack_point(curEnv);
    objectiveMap = new HashMap<>(stack.pop());
  }

  @Override
  public Optional<Rational> upper(int handle, Rational epsilon) {
    return getValue(handle);
  }

  @Override
  public Optional<Rational> lower(int handle, Rational epsilon) {
    return getValue(handle);
  }

  private Optional<Rational> getValue(int handle) {
    // todo: use epsilon if the bound is non-strict.
    assert objectiveMap.get(handle) != null;
    assert objectives != null;
    assert objectives.get(objectiveMap.get(handle)) != null;

    long objective = objectives.get(objectiveMap.get(handle));
    int isUnbounded = msat_objective_value_is_unbounded(curEnv, objective, MSAT_OPTIMUM);
    if (isUnbounded == 1) {
      return Optional.empty();
    }
    assert isUnbounded == 0;
    String objectiveValue = msat_objective_value_repr(curEnv, objective, MSAT_OPTIMUM);
    return Optional.of(Rational.ofString(objectiveValue));
  }

  @Override
  public Model getModel() throws SolverException {

    // Get to the last objective in the stack.
    // todo: code duplication.
    long it = msat_create_objective_iterator(curEnv);
    long[] objectivePtr = new long[1];
    while (msat_objective_iterator_has_next(it) != 0) {
      int status = msat_objective_iterator_next(it, objectivePtr);
      assert status == 0;
    }
    msat_destroy_objective_iterator(it);
    assert objectivePtr[0] != 0;

    msat_set_model(curEnv, objectivePtr[0]);
    return super.getModel();
  }
}
