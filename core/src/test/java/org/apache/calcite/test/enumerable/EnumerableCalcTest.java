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
package org.apache.calcite.test.enumerable;

import org.apache.calcite.adapter.java.ReflectiveSchema;
import org.apache.calcite.sql.fun.SqlStdOperatorTable;
import org.apache.calcite.test.CalciteAssert;
import org.apache.calcite.test.JdbcTest;

import org.junit.jupiter.api.Test;

/**
 * Unit test for
 * {@link org.apache.calcite.adapter.enumerable.EnumerableCalc}
 */
public class EnumerableCalcTest {

  /**
   * Test case for
   * <a href="https://issues.apache.org/jira/browse/CALCITE-3536">[CALCITE-3536]
   * NPE when executing plan with Coalesce due to wrong NullAs strategy</a>.
   */
  @Test public void testCoalesceImplementation() {
    CalciteAssert.that()
        .withSchema("s", new ReflectiveSchema(new JdbcTest.HrSchema()))
        .query("?")
        .withRel(
            builder -> builder
                .scan("s", "emps")
                .project(
                  builder.call(
                    SqlStdOperatorTable.COALESCE,
                    builder.field("commission"),
                    builder.literal(0)))
                .build()
        )
        .planContains("inp4_ != null ? inp4_.intValue() : 0;")
        .returnsUnordered(
            "_f0=0",
            "_f0=250",
            "_f0=500",
            "_f0=1000");
  }
}
