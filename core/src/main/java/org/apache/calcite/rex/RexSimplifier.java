package org.apache.calcite.rex;

public interface RexSimplifier {
  RexNode simplify(RexNode input);
}
