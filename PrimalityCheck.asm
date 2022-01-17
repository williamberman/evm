
======= PrimalityCheck.sol:PrimalityCheck =======
EVM assembly:
    /* "PrimalityCheck.sol":64:236  contract PrimalityCheck {... */
  mstore(0x40, 0x80)
  callvalue
  dup1
  iszero
  tag_1
  jumpi
  0x00
  dup1
  revert
tag_1:
  pop
  dataSize(sub_0)
  dup1
  dataOffset(sub_0)
  0x00
  codecopy
  0x00
  return
stop

/ * 
  Takes jump
  Does not take jump
  Take jump
*/
sub_0: assembly {
        /* "PrimalityCheck.sol":64:236  contract PrimalityCheck {... */
      mstore(0x40, 0x80)
      callvalue
      dup1
      iszero
      tag_1
      /* Does take -- Has to in order to execute the function */
      jumpi
      0x00
      dup1
      revert
    tag_1:
      pop
      /* Does not take -- The calldata length is concrete and we know it's greater than 4 */
      jumpi(tag_2, lt(calldatasize, 0x04))
      shr(0xe0, calldataload(0x00))
      dup1
      0xd5a24249
      eq
      tag_3
      /* We end up taking both the branches here. We should be able to simplify the expression and only take the jump. */
      jumpi
    tag_2:
      0x00
      dup1
      /* We know then that this is the first revert */
      revert
        /* "PrimalityCheck.sol":94:234  function factor(uint x, uint y) public pure  {... */
    tag_3:
      tag_4
      0x04
      dup1
      calldatasize
      sub
      dup2
      add
      swap1
      tag_5
      swap2
      swap1
      tag_6
      jump	// in
    tag_5:
      tag_7
      jump	// in
    tag_4:
      stop
    tag_7:
        /* "PrimalityCheck.sol":159:160  x */
      dup2
        /* "PrimalityCheck.sol":155:156  1 */
      0x01
        /* "PrimalityCheck.sol":155:160  1 < x */
      lt
        /* "PrimalityCheck.sol":155:174  1 < x && x < 973013 */
      dup1
      iszero
      tag_9
      jumpi
      pop
        /* "PrimalityCheck.sol":168:174  973013 */
      0x0ed8d5
        /* "PrimalityCheck.sol":164:165  x */
      dup3
        /* "PrimalityCheck.sol":164:174  x < 973013 */
      lt
        /* "PrimalityCheck.sol":155:174  1 < x && x < 973013 */
    tag_9:
        /* "PrimalityCheck.sol":155:183  1 < x && x < 973013 && 1 < y */
      dup1
      iszero
      tag_10
      jumpi
      pop
        /* "PrimalityCheck.sol":182:183  y */
      dup1
        /* "PrimalityCheck.sol":178:179  1 */
      0x01
        /* "PrimalityCheck.sol":178:183  1 < y */
      lt
        /* "PrimalityCheck.sol":155:183  1 < x && x < 973013 && 1 < y */
    tag_10:
        /* "PrimalityCheck.sol":155:197  1 < x && x < 973013 && 1 < y && y < 973013 */
      dup1
      iszero
      tag_11
      jumpi
      pop
        /* "PrimalityCheck.sol":191:197  973013 */
      0x0ed8d5
        /* "PrimalityCheck.sol":187:188  y */
      dup2
        /* "PrimalityCheck.sol":187:197  y < 973013 */
      lt
        /* "PrimalityCheck.sol":155:197  1 < x && x < 973013 && 1 < y && y < 973013 */
    tag_11:
        /* "PrimalityCheck.sol":147:198  require(1 < x && x < 973013 && 1 < y && y < 973013) */
      tag_12
      jumpi
      /* This revert is because of the require */
      0x00
      dup1
      revert
    tag_12:
        /* "PrimalityCheck.sol":220:226  973013 */
      0x0ed8d5
        /* "PrimalityCheck.sol":215:216  y */
      dup2
        /* "PrimalityCheck.sol":213:214  x */
      dup4
        /* "PrimalityCheck.sol":213:216  x*y */
      tag_13
      swap2
      swap1
      tag_14
      jump	// in
    tag_13:
        /* "PrimalityCheck.sol":213:226  x*y != 973013 */
      eq
      iszero
        /* "PrimalityCheck.sol":206:227  assert(x*y != 973013) */
      tag_15
      jumpi
      tag_16
      tag_17
      jump	// in
    tag_16:
    tag_15:
        /* "PrimalityCheck.sol":94:234  function factor(uint x, uint y) public pure  {... */
      pop
      pop
      jump	// out
        /* "#utility.yul":88:205   */
    tag_19:
        /* "#utility.yul":197:198   */
      0x00
        /* "#utility.yul":194:195   */
      dup1
        /* "#utility.yul":187:199   */
      revert
        /* "#utility.yul":334:411   */
    tag_21:
        /* "#utility.yul":371:378   */
      0x00
        /* "#utility.yul":400:405   */
      dup2
        /* "#utility.yul":389:405   */
      swap1
      pop
        /* "#utility.yul":334:411   */
      swap2
      swap1
      pop
      jump	// out
        /* "#utility.yul":417:539   */
    tag_22:
        /* "#utility.yul":490:514   */
      tag_31
        /* "#utility.yul":508:513   */
      dup2
        /* "#utility.yul":490:514   */
      tag_21
      jump	// in
    tag_31:
        /* "#utility.yul":483:488   */
      dup2
        /* "#utility.yul":480:515   */
      eq
        /* "#utility.yul":470:533   */
      tag_32
      jumpi
        /* "#utility.yul":529:530   */
      0x00
        /* "#utility.yul":526:527   */
      dup1
        /* "#utility.yul":519:531   */
      revert
        /* "#utility.yul":470:533   */
    tag_32:
        /* "#utility.yul":417:539   */
      pop
      jump	// out
        /* "#utility.yul":545:684   */
    tag_23:
        /* "#utility.yul":591:596   */
      0x00
        /* "#utility.yul":629:635   */
      dup2
        /* "#utility.yul":616:636   */
      calldataload
        /* "#utility.yul":607:636   */
      swap1
      pop
        /* "#utility.yul":645:678   */
      tag_34
        /* "#utility.yul":672:677   */
      dup2
        /* "#utility.yul":645:678   */
      tag_22
      jump	// in
    tag_34:
        /* "#utility.yul":545:684   */
      swap3
      swap2
      pop
      pop
      jump	// out
        /* "#utility.yul":690:1164   */
    tag_6:
        /* "#utility.yul":758:764   */
      0x00
        /* "#utility.yul":766:772   */
      dup1
        /* "#utility.yul":815:817   */
      0x40
        /* "#utility.yul":803:812   */
      dup4
        /* "#utility.yul":794:801   */
      dup6
        /* "#utility.yul":790:813   */
      sub
        /* "#utility.yul":786:818   */
      slt
        /* "#utility.yul":783:902   */
      iszero
      tag_36
      jumpi
        /* "#utility.yul":821:900   */
      tag_37
      tag_19
      jump	// in
    tag_37:
        /* "#utility.yul":783:902   */
    tag_36:
        /* "#utility.yul":941:942   */
      0x00
        /* "#utility.yul":966:1019   */
      tag_38
        /* "#utility.yul":1011:1018   */
      dup6
        /* "#utility.yul":1002:1008   */
      dup3
        /* "#utility.yul":991:1000   */
      dup7
        /* "#utility.yul":987:1009   */
      add
        /* "#utility.yul":966:1019   */
      tag_23
      jump	// in
    tag_38:
        /* "#utility.yul":956:1019   */
      swap3
      pop
        /* "#utility.yul":912:1029   */
      pop
        /* "#utility.yul":1068:1070   */
      0x20
        /* "#utility.yul":1094:1147   */
      tag_39
        /* "#utility.yul":1139:1146   */
      dup6
        /* "#utility.yul":1130:1136   */
      dup3
        /* "#utility.yul":1119:1128   */
      dup7
        /* "#utility.yul":1115:1137   */
      add
        /* "#utility.yul":1094:1147   */
      tag_23
      jump	// in
    tag_39:
        /* "#utility.yul":1084:1147   */
      swap2
      pop
        /* "#utility.yul":1039:1157   */
      pop
        /* "#utility.yul":690:1164   */
      swap3
      pop
      swap3
      swap1
      pop
      jump	// out
        /* "#utility.yul":1170:1350   */
    tag_24:
        /* "#utility.yul":1218:1295   */
      0x4e487b7100000000000000000000000000000000000000000000000000000000
        /* "#utility.yul":1215:1216   */
      0x00
        /* "#utility.yul":1208:1296   */
      mstore
        /* "#utility.yul":1315:1319   */
      0x11
        /* "#utility.yul":1312:1313   */
      0x04
        /* "#utility.yul":1305:1320   */
      mstore
        /* "#utility.yul":1339:1343   */
      0x24
        /* "#utility.yul":1336:1337   */
      0x00
        /* "#utility.yul":1329:1344   */
      revert
        /* "#utility.yul":1356:1704   */
    tag_14:
        /* "#utility.yul":1396:1403   */
      0x00
        /* "#utility.yul":1419:1439   */
      tag_42
        /* "#utility.yul":1437:1438   */
      dup3
        /* "#utility.yul":1419:1439   */
      tag_21
      jump	// in
    tag_42:
        /* "#utility.yul":1414:1439   */
      swap2
      pop
        /* "#utility.yul":1453:1473   */
      tag_43
        /* "#utility.yul":1471:1472   */
      dup4
        /* "#utility.yul":1453:1473   */
      tag_21
      jump	// in
    tag_43:
        /* "#utility.yul":1448:1473   */
      swap3
      pop
        /* "#utility.yul":1641:1642   */
      dup2
        /* "#utility.yul":1573:1639   */
      0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
        /* "#utility.yul":1569:1643   */
      div
        /* "#utility.yul":1566:1567   */
      dup4
        /* "#utility.yul":1563:1644   */
      gt
        /* "#utility.yul":1558:1559   */
      dup3
        /* "#utility.yul":1551:1560   */
      iszero
        /* "#utility.yul":1544:1561   */
      iszero
        /* "#utility.yul":1540:1645   */
      and
        /* "#utility.yul":1537:1668   */
      iszero
      tag_44
      jumpi
        /* "#utility.yul":1648:1666   */
      tag_45
      tag_24
      jump	// in
    tag_45:
        /* "#utility.yul":1537:1668   */
    tag_44:
        /* "#utility.yul":1696:1697   */
      dup3
        /* "#utility.yul":1693:1694   */
      dup3
        /* "#utility.yul":1689:1698   */
      mul
        /* "#utility.yul":1678:1698   */
      swap1
      pop
        /* "#utility.yul":1356:1704   */
      swap3
      swap2
      pop
      pop
      jump	// out
        /* "#utility.yul":1710:1890   */
    tag_17:
        /* "#utility.yul":1758:1835   */
      0x4e487b7100000000000000000000000000000000000000000000000000000000
        /* "#utility.yul":1755:1756   */
      0x00
        /* "#utility.yul":1748:1836   */
      mstore
        /* "#utility.yul":1855:1859   */
      0x01
        /* "#utility.yul":1852:1853   */
      0x04
        /* "#utility.yul":1845:1860   */
      mstore
        /* "#utility.yul":1879:1883   */
      0x24
        /* "#utility.yul":1876:1877   */
      0x00
        /* "#utility.yul":1869:1884   */
      revert

    auxdata: 0xa26469706673582212202c667a96599f0a0921c5454871e3ebdb6434748a412b3bf97324ce0d32ec5fe864736f6c63430008090033
}

