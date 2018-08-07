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
package org.apache.calcite.test;

import org.apache.calcite.DataContext;
import org.apache.calcite.adapter.java.JavaTypeFactory;
import org.apache.calcite.jdbc.JavaTypeFactoryImpl;
import org.apache.calcite.linq4j.QueryProvider;
import org.apache.calcite.plan.RelOptPredicateList;
import org.apache.calcite.rel.type.RelDataType;
import org.apache.calcite.rel.type.RelDataTypeFactory;
import org.apache.calcite.rel.type.RelDataTypeSystem;
import org.apache.calcite.rex.RexBuilder;
import org.apache.calcite.rex.RexDynamicParam;
import org.apache.calcite.rex.RexExecutor;
import org.apache.calcite.rex.RexExecutorImpl;
import org.apache.calcite.rex.RexLiteral;
import org.apache.calcite.rex.RexNode;
import org.apache.calcite.rex.RexSimplify;
import org.apache.calcite.rex.RexSimplify2;
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.sql.fun.SqlStdOperatorTable;
import org.apache.calcite.sql.type.SqlTypeName;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;

import java.util.TimeZone;

/**
 * This class provides helper methods to build rex expressions.
 */
public class RexProgramBuilderBase {
  protected final static int MAX_FIELDS = 10;

  protected JavaTypeFactory typeFactory;
  protected RexBuilder rexBuilder;
  protected RexLiteral trueLiteral;
  protected RexLiteral falseLiteral;
  protected RexNode nullLiteral;
  protected RexNode unknownLiteral;
  protected RexSimplify2 simplify;
  protected RelDataType nullableBool;
  protected RelDataType nonNullableBool;
  protected RexLiteral nullBool;
  protected RelDataType nullableInt;
  protected RelDataType nonNullableInt;
  protected RexExecutor executor;

  protected RexDynamicParam dynamicBoolParam;
  protected RexDynamicParam dynamicIntParam;

  /**
   * Dummy data context for test.
   */
  private static class DummyTestDataContext implements DataContext {
    private final ImmutableMap<String, Object> map;

    DummyTestDataContext() {
      this.map =
          ImmutableMap.of(
              Variable.TIME_ZONE.camelName, TimeZone.getTimeZone("America/Los_Angeles"),
              Variable.CURRENT_TIMESTAMP.camelName, 1311120000000L);
    }

    public SchemaPlus getRootSchema() {
      return null;
    }

    public JavaTypeFactory getTypeFactory() {
      return null;
    }

    public QueryProvider getQueryProvider() {
      return null;
    }

    public Object get(String name) {
      return map.get(name);
    }
  }

  public void setUp() {
    typeFactory = new JavaTypeFactoryImpl(RelDataTypeSystem.DEFAULT);
    rexBuilder = new RexBuilder(typeFactory);
    executor =
        new RexExecutorImpl(new DummyTestDataContext());
    simplify =
        new RexSimplify2(rexBuilder, RelOptPredicateList.EMPTY, false, executor)
            .withParanoid(true);
    trueLiteral = rexBuilder.makeLiteral(true);
    falseLiteral = rexBuilder.makeLiteral(false);

    nonNullableInt = typeFactory.createSqlType(SqlTypeName.INTEGER);
    nullableInt = typeFactory.createTypeWithNullability(nonNullableInt, true);

    nullLiteral = rexBuilder.makeNullLiteral(nonNullableInt);
    unknownLiteral = rexBuilder.makeNullLiteral(trueLiteral.getType());

    nonNullableBool = typeFactory.createSqlType(SqlTypeName.BOOLEAN);
    nullableBool = typeFactory.createTypeWithNullability(nonNullableBool, true);
    nullBool = rexBuilder.makeNullLiteral(nullableBool);
    {
      RelDataTypeFactory.Builder builder = typeFactory.builder();
      for (int i = 0; i < MAX_FIELDS; i++) {
        builder.add("bool" + i, nullableBool);
      }
      for (int i = 0; i < MAX_FIELDS; i++) {
        builder.add("notNullBool" + i, nonNullableBool);
      }
      dynamicBoolParam = rexBuilder.makeDynamicParam(builder.build(), 0);
    }
    {
      RelDataTypeFactory.Builder builder = typeFactory.builder();
      for (int i = 0; i < MAX_FIELDS; i++) {
        builder.add("int" + i, nullableInt);
      }
      for (int i = 0; i < MAX_FIELDS; i++) {
        builder.add("notNullInt" + i, nonNullableInt);
      }
      dynamicIntParam = rexBuilder.makeDynamicParam(builder.build(), 0);
    }
  }

  protected RexNode isNull(RexNode node) {
    return rexBuilder.makeCall(SqlStdOperatorTable.IS_NULL, node);
  }

  protected RexNode isNotNull(RexNode node) {
    return rexBuilder.makeCall(SqlStdOperatorTable.IS_NOT_NULL, node);
  }

  protected RexNode isFalse(RexNode node) {
    return rexBuilder.makeCall(SqlStdOperatorTable.IS_FALSE, node);
  }

  protected RexNode isNotFalse(RexNode node) {
    return rexBuilder.makeCall(SqlStdOperatorTable.IS_NOT_FALSE, node);
  }

  protected RexNode isTrue(RexNode node) {
    return rexBuilder.makeCall(SqlStdOperatorTable.IS_TRUE, node);
  }

  protected RexNode isNotTrue(RexNode node) {
    return rexBuilder.makeCall(SqlStdOperatorTable.IS_NOT_TRUE, node);
  }

  protected RexNode nullIf(RexNode node1, RexNode node2) {
    return rexBuilder.makeCall(SqlStdOperatorTable.NULLIF, node1, node2);
  }

  protected RexNode not(RexNode node) {
    return rexBuilder.makeCall(SqlStdOperatorTable.NOT, node);
  }

  protected RexNode and(RexNode... nodes) {
    return and(ImmutableList.copyOf(nodes));
  }

  protected RexNode and(Iterable<? extends RexNode> nodes) {
    // Does not flatten nested ANDs. We want test input to contain nested ANDs.
    return rexBuilder.makeCall(SqlStdOperatorTable.AND,
        ImmutableList.copyOf(nodes));
  }

  protected RexNode or(RexNode... nodes) {
    return or(ImmutableList.copyOf(nodes));
  }

  protected RexNode or(Iterable<? extends RexNode> nodes) {
    // Does not flatten nested ORs. We want test input to contain nested ORs.
    return rexBuilder.makeCall(SqlStdOperatorTable.OR,
        ImmutableList.copyOf(nodes));
  }

  protected RexNode case_(RexNode... nodes) {
    return rexBuilder.makeCall(SqlStdOperatorTable.CASE, nodes);
  }

  protected RexNode cast(RexNode e, RelDataType type) {
    return rexBuilder.makeCast(type, e);
  }

  protected RexNode eq(RexNode n1, RexNode n2) {
    return rexBuilder.makeCall(SqlStdOperatorTable.EQUALS, n1, n2);
  }

  protected RexNode ne(RexNode n1, RexNode n2) {
    return rexBuilder.makeCall(SqlStdOperatorTable.NOT_EQUALS, n1, n2);
  }

  protected RexNode le(RexNode n1, RexNode n2) {
    return rexBuilder.makeCall(SqlStdOperatorTable.LESS_THAN_OR_EQUAL, n1, n2);
  }

  protected RexNode lt(RexNode n1, RexNode n2) {
    return rexBuilder.makeCall(SqlStdOperatorTable.LESS_THAN, n1, n2);
  }

  protected RexNode ge(RexNode n1, RexNode n2) {
    return rexBuilder.makeCall(SqlStdOperatorTable.GREATER_THAN_OR_EQUAL, n1, n2);
  }

  protected RexNode gt(RexNode n1, RexNode n2) {
    return rexBuilder.makeCall(SqlStdOperatorTable.GREATER_THAN, n1, n2);
  }

  protected RexNode plus(RexNode n1, RexNode n2) {
    return rexBuilder.makeCall(SqlStdOperatorTable.PLUS, n1, n2);
  }

  protected RexNode coalesce(RexNode... nodes) {
    return rexBuilder.makeCall(SqlStdOperatorTable.COALESCE, nodes);
  }

  protected RexNode input(RelDataType type, int arg) {
    return rexBuilder.makeInputRef(type, arg);
  }

  protected RexNode vBool() {
    return vBool(0);
  }

  protected RexNode vBool(int arg) {
    return rexBuilder.makeFieldAccess(dynamicBoolParam, arg);
  }

  protected RexNode vBoolNotNull() {
    return vBoolNotNull(0);
  }

  protected RexNode vBoolNotNull(int arg) {
    return vBool(arg + MAX_FIELDS);
  }

  protected RexNode vInt() {
    return vInt(0);
  }

  protected RexNode vInt(int arg) {
    return rexBuilder.makeFieldAccess(dynamicIntParam, arg);
  }

  protected RexNode vIntNotNull() {
    return vIntNotNull(0);
  }

  protected RexNode vIntNotNull(int arg) {
    return vInt(arg + MAX_FIELDS);
  }

  protected RexNode literal(int value) {
    return rexBuilder.makeLiteral(value, nonNullableInt, false);
  }

  protected RexNode in(RexNode node, RexNode... nodes){
    return rexBuilder.makeCall(SqlStdOperatorTable.IN,
        ImmutableList.<RexNode>builder().add(node).add(nodes).build());
  }
}

// End RexProgramBuilderBase.java
