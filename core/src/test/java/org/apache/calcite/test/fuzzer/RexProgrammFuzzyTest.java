/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to you under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.calcite.test.fuzzer;

import org.apache.calcite.plan.RelOptPredicateList;
import org.apache.calcite.rel.type.RelDataType;
import org.apache.calcite.rex.RexCall;
import org.apache.calcite.rex.RexExecutorImpl;
import org.apache.calcite.rex.RexInputRef;
import org.apache.calcite.rex.RexNode;
import org.apache.calcite.rex.RexSimplify;
import org.apache.calcite.rex.RexSimplify2;
import org.apache.calcite.rex.RexUtil;
import org.apache.calcite.sql.SqlOperator;
import org.apache.calcite.sql.fun.SqlStdOperatorTable;
import org.apache.calcite.sql.type.SqlTypeName;
import org.apache.calcite.test.RexProgramBuilderBase;

import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.PriorityQueue;
import java.util.Random;
import java.util.Set;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * Validates that {@link org.apache.calcite.rex.RexSimplify} is able to deal with
 * randomized {@link RexNode}.
 * Note: the default fuzzing time is 5 seconds to keep overall test duration reasonable.
 * You might increase
 */
public class RexProgrammFuzzyTest extends RexProgramBuilderBase {
  private static final int TEST_DURATION = Integer.getInteger("rex.fuzzing.duration", 10);
  private static final int MAX_FAILURES =
      Integer.getInteger("rex.fuzzing.max.failures", 5000);
  private static final int TOPN_SLOWEST =
      Integer.getInteger("rex.fuzzing.max.slowest", 5);
  private static final long SEED =
      Long.getLong("rex.fuzzing.seed", 0);

  private PriorityQueue<SimplifyTask> slowestTasks;

  /**
   * A bounded variation of {@link PriorityQueue}
   *
   * @param <E> the type of elements held in this collection
   */
  private static class TopN<E extends Comparable<E>> extends PriorityQueue<E> {
    private final int n;

    private TopN(int n) {
      this.n = n;
    }

    @Override public boolean offer(E o) {
      if (size() == n) {
        E peek = peek();
        if (peek != null && peek.compareTo(o) > 0) {
          return false;
        }
        poll();
      }
      return super.offer(o);
    }

    @Override public Iterator<E> iterator() {
      throw new UnsupportedOperationException("Order of elements is not defined, please use .peek");
    }
  }

  @Before public void setUp() {
    super.setUp();
  }

  @Test public void testAlwaysTrueFalse() {
    RelDataType in = typeFactory.createSqlType(SqlTypeName.BOOLEAN);

    SqlOperator[] operators = new SqlOperator[]{
        SqlStdOperatorTable.NOT,
        SqlStdOperatorTable.IS_FALSE,
        SqlStdOperatorTable.IS_NOT_FALSE,
        SqlStdOperatorTable.IS_TRUE,
        SqlStdOperatorTable.IS_NOT_TRUE,
        SqlStdOperatorTable.IS_NULL,
        SqlStdOperatorTable.IS_NOT_NULL,
        SqlStdOperatorTable.IS_UNKNOWN,
        SqlStdOperatorTable.IS_NOT_UNKNOWN
    };
    for (boolean argNullability : new boolean[]{true, false}) {
      RexInputRef arg = rexBuilder.makeInputRef(
          typeFactory.createTypeWithNullability(
              in, argNullability),
          argNullability ? 10 : 0);
      for (SqlOperator op1 : operators) {
        RexNode n1 = rexBuilder.makeCall(op1, arg);
        checkTrueFalse(n1);
        for (SqlOperator op2 : operators) {
          RexNode n2 = rexBuilder.makeCall(op2, n1);
          checkTrueFalse(n2);
          for (SqlOperator op3 : operators) {
            RexNode n3 = rexBuilder.makeCall(op3, n2);
            checkTrueFalse(n3);
            for (SqlOperator op4 : operators) {
              RexNode n4 = rexBuilder.makeCall(op4, n3);
              checkTrueFalse(n4);
            }
          }
        }
      }
    }
  }

  private void checkTrueFalse(RexNode node) {
    RexNode opt;
    try {
      long start = System.nanoTime();
      opt = this.simplify.simplify(node);
      long end = System.nanoTime();
      if (end - start > 1000 && slowestTasks != null) {
        slowestTasks.add(new SimplifyTask(node, opt, end - start));
      }
    } catch (AssertionError a) {
      String message = a.getMessage();
      if (message != null && message.startsWith("result mismatch")) {
        throw a;
      }
      throw new IllegalStateException("Unable to simplify " + node, a);
    } catch (Throwable t) {
      throw new IllegalStateException("Unable to simplify " + node, t);
    }
    if (trueLiteral.equals(opt)) {
      String msg = node.toString();
      assertFalse(msg + " optimizes to TRUE, isAlwaysFalse MUST not be true",
          node.isAlwaysFalse());
//      This is a missing optimization, not a bug
//      assertFalse(msg + " optimizes to TRUE, isAlwaysTrue MUST be true",
//          !node.isAlwaysTrue());
    }
    if (falseLiteral.equals(opt)) {
      String msg = node.toString();
      assertFalse(msg + " optimizes to FALSE, isAlwaysTrue MUST not be true",
          node.isAlwaysTrue());
//      This is a missing optimization, not a bug
//      assertFalse(msg + " optimizes to FALSE, isAlwaysFalse MUST be true",
//          !node.isAlwaysFalse());
    }
    if (nullLiteral.equals(opt)) {
      String msg = node.toString();
      assertFalse(msg + " optimizes to NULL, isAlwaysTrue MUST be FALSE",
          node.isAlwaysTrue());
      assertFalse(msg + " optimizes to NULL, isAlwaysFalse MUST be FALSE",
          node.isAlwaysFalse());
    }
    if (node.isAlwaysTrue()) {
      String msg = node.toString();
      assertEquals(msg + " isAlwaysTrue, so it should simplify to TRUE",
          trueLiteral, opt);
    }
    if (node.isAlwaysFalse()) {
      String msg = node.toString();
      assertEquals(msg + " isAlwaysFalse, so it should simplify to FALSE",
          falseLiteral, opt);
    }
  }

  @Test public void testFuzzy() {
    if (TEST_DURATION == 0) {
      return;
    }
    slowestTasks = new TopN<>(TOPN_SLOWEST);
    Random r = new Random();
    if (SEED != 0) {
      r.setSeed(SEED);
    }
    long start = System.currentTimeMillis();
    long deadline = start + TimeUnit.SECONDS.toMillis(TEST_DURATION);
    List<Throwable> exceptions = new ArrayList<>();
    Set<String> duplicates = new HashSet<>();
    int total = 0;
    int dup = 0;
    int fail = 0;
    RexFuzzer fuzzer = new RexFuzzer(rexBuilder, typeFactory);
    while (System.currentTimeMillis() < deadline && exceptions.size() < MAX_FAILURES) {
      long seed = r.nextLong();
      r.setSeed(seed);
      try {
        total++;
        generateRexAndCheckTrueFalse(fuzzer, r);
      } catch (Throwable e) {
        if (!duplicates.add(e.getMessage())) {
          dup++;
          // known exception, nothing to see here
          continue;
        }
        fail++;
        StackTraceElement[] stackTrace = e.getStackTrace();
        for (int j = 0; j < stackTrace.length; j++) {
          if (stackTrace[j].getClassName().endsWith("RexProgramTest")) {
            e.setStackTrace(Arrays.copyOf(stackTrace, j + 1));
            break;
          }
        }
        e.addSuppressed(new Throwable("seed " + seed) {
          @Override public synchronized Throwable fillInStackTrace() {
            return this;
          }
        });
        exceptions.add(e);
      }
    }
    System.out.println("total           = " + total);
    System.out.println("failed          = " + fail);
    System.out.println("duplicate fails = " + dup);
    long rate = total * 1000 / (System.currentTimeMillis() - start);
    System.out.println("fuzz rate       = " + rate + " per second");

    System.out.println("The 5 slowest to simplify nodes were");
    SimplifyTask task;
    while ((task = slowestTasks.poll()) != null) {
      System.out.println();
      System.out.println(task.duration / 1000 + " us");
      System.out.println("      " + task.node.toString());
      System.out.println("    =>" + task.result.toString());
    }

    if (exceptions.isEmpty()) {
      return;
    }

    // Print the shortest fails first
    exceptions.sort(Comparator.<Throwable>comparingInt(t -> t.getMessage().length())
        .thenComparing(Throwable::getMessage));

    for (Throwable exception : exceptions) {
      exception.printStackTrace();
    }

    Throwable ex = exceptions.get(0);
    if (ex instanceof Error) {
      throw (Error) ex;
    }
    throw new RuntimeException("Exception in testFuzzy", ex);
  }

  private void generateRexAndCheckTrueFalse(RexFuzzer fuzzer, Random r) {
    RexNode expression = fuzzer.getExpression(r, r.nextInt(10));
    checkTrueFalse(expression);
  }

  @Test public void singleFuzzyTest() {
    Random r = new Random();
    r.setSeed(-6539797260474794707L);
//    r.setSeed(-7306345575755792631L);
    RexFuzzer fuzzer = new RexFuzzer(rexBuilder, typeFactory);
    generateRexAndCheckTrueFalse(fuzzer, r);
  }


  private void assertSimplifies(String expected, RexNode node) {
    RexNode opt = this.simplify.simplify(node);
    assertEquals(node.toString(), expected, opt.toString());
  }

  /**
   * Manually coded tests go here. It ensures the cases identified by fuzzer are kept
   * even in case fuzzer implementation changes over time.
   */
  @Test public void testSimplifies() {
    assertSimplifies("true", isNull(nullBool));
    assertSimplifies("null", not(nullBool));
    assertSimplifies("false", not(trueLiteral));
    assertSimplifies("true", not(falseLiteral));
    assertSimplifies("false", isFalse(nullLiteral));
    // TODO: -42 ?
    assertSimplifies("-(42)",
        rexBuilder.makeCall(SqlStdOperatorTable.UNARY_MINUS, literal(42)));
    assertSimplifies("42",
        rexBuilder.makeCall(SqlStdOperatorTable.UNARY_MINUS,
            rexBuilder.makeCall(SqlStdOperatorTable.UNARY_MINUS, literal(42))));

    assertSimplifies("IS NOT FALSE(?0.bool0)", isFalse(isFalse(vBool())));
    assertSimplifies("IS NOT FALSE(?0.bool0)", isFalse(isFalse(isFalse(isFalse(vBool())))));
    assertSimplifies("null", rexBuilder.makeCall(SqlStdOperatorTable.UNARY_MINUS, nullLiteral));
    assertSimplifies("IS NULL(?0.int0)", isNull(vInt()));
    assertSimplifies("true", isNotNull(vIntNotNull()));
    assertSimplifies("false", isFalse(vInt()));
    assertSimplifies("false", isFalse(vIntNotNull()));
    assertSimplifies("IS FALSE(?0.bool0)", isFalse(vBool()));
    assertSimplifies("IS FALSE(?0.bool0)", isFalse(vBool()));
    assertSimplifies("NOT(?0.notNullBool0)", isFalse(vBoolNotNull()));
    // {$34=-1, $31=-1, $13=true}, COALESCE(=($34, null), IS NOT FALSE($31), $13) yielded true,
    // and $31 yielded -1
    assertSimplifies("true",
        coalesce(
            eq(input(nullableInt, 34), nullLiteral),
            isNotFalse(input(nonNullableInt, 31)), input(nullableBool, 13)));
    assertSimplifies("true",
        rexBuilder.makeCall(SqlStdOperatorTable.IS_NOT_TRUE, nullLiteral));
    assertSimplifies("true",
        rexBuilder.makeCall(SqlStdOperatorTable.IS_NOT_FALSE, nullLiteral));
    assertSimplifies("false", and(falseLiteral, falseLiteral));
    assertSimplifies("false", and(falseLiteral, trueLiteral));
    assertSimplifies("false", and(falseLiteral, nullLiteral));
    assertSimplifies("true", and(trueLiteral, trueLiteral));
    assertSimplifies("null", and(trueLiteral, nullLiteral));
    assertSimplifies("null", and(nullLiteral, nullLiteral));
    assertSimplifies("true",
        or(
            ne(nullBool, input(nonNullableBool, 2)), // => NULL
            eq(isNotNull(nullBool), falseLiteral), // => TRUE
            falseLiteral));
    assertSimplifies("true",
        le(coalesce(falseLiteral, nullBool),
            or(
                ne(nullBool, input(nonNullableBool, 2)),
                le(nullBool, nullBool),
                eq(isNotNull(nullBool), isFalse(nullBool)),
                input(nullableBool, 12))));
    assertSimplifies("OR(null, $11, AND(null, $14))",
        or(nullLiteral,
            or(
                input(nullableBool, 11),
                and(nullLiteral,
                    input(nullableBool, 14)), nullLiteral)));
    assertSimplifies("true", gt(trueLiteral, falseLiteral));
    assertSimplifies("false",
        and(
            input(nullableBool, 14),
            isNotNull(and(trueLiteral, trueLiteral, nullLiteral)),
            isNotNull(coalesce(nullLiteral)),
            vBoolNotNull()));
    assertSimplifies("null", ge(nullLiteral, falseLiteral));
    assertSimplifies("false",
        isNotNull(
            ge(
                coalesce(nullLiteral),
                falseLiteral)));
    assertSimplifies("true",
        isNull(
            ge(
                coalesce(nullLiteral),
                falseLiteral)));
  }

  @Test public void testAndSimplifies() {
//    assertSimplifies("false", isTrue(and(vBool(), nullBool)));
//    assertSimplifies("true", isNotTrue(and(vBool(), nullBool)));
//    assertSimplifies("IS FALSE(?0.bool0)", isFalse(and(vBool(), nullBool)));
//    assertSimplifies("IS NOT FALSE(?0.bool0)", isNotFalse(and(vBool(), nullBool)));
//    assertSimplifies("IS NOT FALSE(?0.bool0)", isNull(and(vBool(), nullBool)));
//    assertSimplifies("IS FALSE(?0.bool0)", isNotNull(and(vBool(), nullBool)));

//    assertEquals("AND(=(?0.bool0, true), =(?0.bool2, true))",
//        RexUtil.simplify(rexBuilder, eq(nullBool, input(nullableBool, 1)), true).toString()
//        );
//    assertSimplifies("asdf", eq(nullBool, input(nullableBool, 1)));
//    RexNode testNode = and(
//        trueLiteral,//eq(input(nullableInt, 0), literal(42)),
//        eq(input(nullableInt, 0), literal(42)));
//    assertSimplifies("IN(?0.int0, 42, 43)",
//        in(vInt(), literal(42), literal(43)));
//    assertSimplifies("IS FALSE(=(?0.int0, 42))",
//        isFalse(eq(vInt(), literal(42))));

//    assertSimplifies("AND(OR(?0.bool1, AND(?0.bool3, NOT(?0.bool2))), NOT(?0.bool0))",
//        not(or(
//            vBoolNotNull(0),
//            not(or(
//                vBoolNotNull(1),
//                not(or(
//                    vBoolNotNull(2),
//                    not(vBoolNotNull(3)))))))));

    RexNode i0 = input(nullableInt, 0);
    RexNode i1 = input(nullableInt, 1);
//    RexNode testNode = and(
//        trueLiteral,//eq(input(nullableInt, 0), literal(42)),
//        eq(input(nullableBool, 2), eq(i1, i1)),
//        eq(i0, literal(42)),
//        eq(i1, literal(43))
////        eq(i0, i1)
//        );
//    RexNode testNode = and(
//        eq(i0, literal(41)),
//        eq(i0, literal(42))
//        //not(in(i0, literal(42), literal(43)))
//    );
    RexNode testNode = (
//        eq(i0, literal(41)),
//        isNotNull(i0)
        isTrue(falseLiteral)
        //not(in(i0, literal(42), literal(43)))
    );
//    RexNode testNode = not(or(
//        vBool(0),
//        not(or(
//            vBool(1),
//            not(or(
//                vBool(2),
//                not(vBool(3))))))));
    RexSimplify simplifyOld =
        new RexSimplify(rexBuilder, RelOptPredicateList.EMPTY, true, executor)
            .withParanoid(true);

//    System.out.println("old = " + RexUtil.simplify(rexBuilder, testNode,false).toString());
    String old = simplifyOld.simplify(isTrue(testNode)).toString();
    String newRes = simplify.withUnknownAsFalse(true).simplify(testNode).toString();

    System.out.println("old = " + old);
    System.out.println("new = " + newRes);
    assertEquals(testNode.toString(), old, newRes);

    assertSimplifies("AND(=(?0.bool0, true), =(?0.bool1, true))",
        and(eq(vBool(0), trueLiteral), eq(vBool(1), trueLiteral)));
    assertSimplifies("AND(=(?0.bool0, true), =(?0.bool1, true))",
        isTrue(and(eq(vBool(0), trueLiteral), eq(vBool(1), trueLiteral)))
        );

    assertSimplifies("false", and(vBoolNotNull(), not(vBoolNotNull())));
    assertSimplifies("AND(?0.bool0, NOT(?0.bool0))", and(vBool(), not(vBool())));

    assertSimplifies("true", and(trueLiteral, trueLiteral));
    assertSimplifies("false", and(nullLiteral, falseLiteral));
    assertSimplifies("null", and(nullLiteral, not(nullLiteral)));
    // TODO: optimize to IS NOT NULL($100)
    assertSimplifies("AND(?0.bool0, NOT(?0.bool0))",
        and(vBool(), not(vBool())));
    // TODO: optimize to false
    assertSimplifies("AND(?0.notNullBool01, OR(NOT(?0.notNullBool01), NOT(?0.notNullBool21)))", and(
        vBoolNotNull(0),
        not(and(vBoolNotNull(0), vBoolNotNull(1)))));
    assertSimplifies("?0.notNullBool01", isTrue(vBoolNotNull()));
    assertSimplifies("IS TRUE(?0.bool0)", isTrue(vBool()));

    assertSimplifies("IS NOT NULL(COALESCE(?0.bool0, ?0.bool2))",
        isNotNull(coalesce(vBool(0), vBool(1))));
    // TODO: optimize to AND(IS NOT NULL(?0.bool0), IS NOT NULL(?0.bool2))
    assertSimplifies("IS NULL(COALESCE(?0.bool0, ?0.bool2))",
        isNull(coalesce(vBool(0), vBool(1))));

    assertSimplifies("OR(IS FALSE(?0.bool0), IS NOT NULL(?0.bool2))",
        isNotNull(coalesce(and(vBool(0), nullBool), vBool(1))));
    assertSimplifies("true",
        isNotNull(coalesce(and(vBool(0), nullBool), vBoolNotNull(1))));
    assertSimplifies("false",
        isNull(coalesce(and(vBool(0), nullBool), vBoolNotNull(1))));
  }

  @Test public void testComparableSimplifies() {
    assertSimplifies("true", ge(trueLiteral, falseLiteral));
    assertSimplifies("null", ge(trueLiteral, nullBool));
    assertSimplifies("null", ge(nullBool, nullBool));
  }

  @Test public void alwaysTests() {
    alwaysNull(not(nullBool));
    alwaysFalse(not(trueLiteral));
    alwaysTrue(not(falseLiteral));

    alwaysTrue(isNotFalse(nullBool));
    alwaysFalse(isFalse(nullBool));
  }

  private void alwaysNull(RexNode node) {
    assertFalse(node + " should produce isAlwaysTrue=false", node.isAlwaysTrue());
    assertFalse(node + " should produce isAlwaysFalse=false", node.isAlwaysFalse());
    assertTrue(node + " should produce isAlwaysNull", node.isAlwaysNull());
    checkTrueFalse(node);
  }

  private void alwaysTrue(RexNode node) {
    assertTrue(node + " should produce isAlwaysTrue", node.isAlwaysTrue());
    assertFalse(node + " should produce isAlwaysFalse=false", node.isAlwaysFalse());
    assertFalse(node + " should produce isAlwaysNull=false", node.isAlwaysNull());
    checkTrueFalse(node);
  }

  private void alwaysFalse(RexNode node) {
    assertFalse(node + " should produce isAlwaysTrue=false", node.isAlwaysTrue());
    assertTrue(node + " should produce isAlwaysFalse", node.isAlwaysFalse());
    assertFalse(node + " should produce isAlwaysNull=false", node.isAlwaysNull());
    checkTrueFalse(node);
  }
}

// End RexProgrammFuzzyTest.java
