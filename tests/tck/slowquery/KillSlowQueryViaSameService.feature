# Copyright (c) 2021 vesoft inc. All rights reserved.
#
# This source code is licensed under Apache 2.0 License,
# attached with Common Clause Condition 1.0, found in the LICENSES directory.
Feature: Slow Query Test

  # There should be a least 2 thread to run this test case suite.
  Scenario: Set up slow query
    # Set up a slow query which will be killed later.
    Given a graph with space named "nba"
    When executing query:
      """
      GO 100000 STEPS FROM "Tim Duncan" OVER like
      """
    Then an ExecutionError should be raised at runtime: Execution had been killed

  Scenario: Show all queries and kill all slow queries
    When executing query:
      """
      SHOW QUERIES
      """
    Then the execution should be successful
    When executing query:
      """
      SHOW ALL QUERIES
      """
    Then the execution should be successful
    And wait 20 seconds
    When executing query:
      """
      SHOW ALL QUERIES
      """
    Then the result should be, in order:
      | SessionID | ExecutionPlanID | User   | Host | StartTime | DurationInUSec | Status    | Query                                           |
      | /\d+/     | /\d+/           | "root" | /.*/ | /.*/      | /\d+/          | "RUNNING" | "GO 100000 STEPS FROM \"Tim Duncan\" OVER like" |
    When executing query:
      """
      SHOW ALL QUERIES
      | YIELD $-.SessionID AS sid, $-.ExecutionPlanID AS eid, $-.DurationInUSec AS dur
      WHERE $-.DurationInUSec > 1000 AND $-.`Query` CONTAINS "GO 100000 STEPS";
      """
    Then the result should be, in order:
      | sid   | eid   | dur   |
      | /\d+/ | /\d+/ | /\d+/ |
    When executing query:
      """
      KILL QUERY ()
      """
    Then a SyntaxError should be raised at runtime: syntax error near `)'
    When executing query:
      """
      KILL QUERY (session=123)
      """
    Then a SyntaxError should be raised at runtime: syntax error near `)'
    When executing query:
      """
      KILL QUERY (plan=987654321)
      """
    Then an ExecutionError should be raised at runtime: ExecutionPlanId[987654321] does not exist in current Session.
    When executing query:
      """
      KILL QUERY (session=987654321, plan=987654321)
      """
    Then an ExecutionError should be raised at runtime: SessionId[987654321] does not exist
    When executing query:
      """
      KILL QUERY (session=$-.sid, plan=$-.eid)
      """
    Then an SemanticError should be raised at runtime: `$-.sid', not exist prop `sid'
    When executing query:
      """
      KILL QUERY (plan=$-.eid)
      """
    Then an SemanticError should be raised at runtime: `$-.eid', not exist prop `eid'
    When executing query:
      """
      SHOW ALL QUERIES
      | YIELD $-.SessionID AS sid, $-.`Query` AS eid, $-.DurationInUSec AS dur WHERE $-.DurationInUSec > 10000000
      | ORDER BY $-.dur
      | KILL QUERY (session=$-.sid, plan=$-.eid)
      """
    Then an SemanticError should be raised at runtime: $-.eid, Session ID must be an integer but was STRING
    When executing query:
      """
      SHOW ALL QUERIES
      | YIELD $-.SessionID AS sid, $-.ExecutionPlanID AS eid, $-.DurationInUSec AS dur
      WHERE $-.DurationInUSec > 10000000 AND $-.`Query` CONTAINS "GO"
      | ORDER BY $-.dur
      | KILL QUERY(session=$-.sid, plan=$-.eid)
      """
    Then the execution should be successful
