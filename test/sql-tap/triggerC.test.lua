#!/usr/bin/env tarantool
test = require("sqltester")
test:plan(52)

--!./tcltestrunner.lua
-- 2009 August 24
--
-- The author disclaims copyright to this source code.  In place of
-- a legal notice', here is a blessing:
--
--    May you do good and not evil.
--    May you find forgiveness for yourself and forgive others.
--    May you share freely, never taking more than you give.
--
-------------------------------------------------------------------------
--
-- ["set","testdir",[["file","dirname",["argv0"]]]]
-- ["source",[["testdir"],"\/tester.tcl"]]
testprefix = "triggerC"


---------------------------------------------------------------------------
-- Test organization:
--
-- triggerC-1.*: Haphazardly designed trigger related tests that were useful
--               during an upgrade of the triggers sub-system.
--
-- triggerC-2.*:
--
-- triggerC-3.*:
--
-- triggerC-4.*:
--
-- triggerC-5.*: Test that when recursive triggers are enabled DELETE
--               triggers are fired when rows are deleted as part of OR
--               REPLACE conflict resolution. And that they are not fired
--               if recursive triggers are not enabled.
--
-- triggerC-6.*: Test that the recursive_triggers pragma returns correct
--               results when invoked without an argument.
--
-- Enable recursive triggers for this file.
--
test:execsql " PRAGMA recursive_triggers = on "
--sqlite3_db_config_lookaside db 0 0 0
---------------------------------------------------------------------------
-- This block of tests, triggerC-1.*, are not aimed at any specific
-- property of the triggers sub-system. They were created to debug
-- specific problems while modifying SQLite to support recursive
-- triggers. They are left here in case they can help debug the
-- same problems again.
--
test:do_execsql_test(
    "triggerC-1.1",
    [[
        CREATE TABLE t1(a PRIMARY KEY, b, c);
        CREATE TABLE log(t PRIMARY KEY, a1, b1, c1, a2, b2, c2);
        CREATE TRIGGER trig1 BEFORE INSERT ON t1 BEGIN
          INSERT INTO log VALUES('before', NULL, NULL, NULL, new.a, new.b, new.c);
        END;
        CREATE TRIGGER trig2 AFTER INSERT ON t1 BEGIN
          INSERT INTO log VALUES('after', NULL, NULL, NULL, new.a, new.b, new.c);
        END;
        CREATE TRIGGER trig3 BEFORE UPDATE ON t1 BEGIN
          INSERT INTO log VALUES('before', old.a,old.b,old.c, new.a,new.b,new.c);
        END;
        CREATE TRIGGER trig4 AFTER UPDATE ON t1 BEGIN
          INSERT INTO log VALUES('after', old.a,old.b,old.c, new.a,new.b,new.c);
        END;

        CREATE TRIGGER trig5 BEFORE DELETE ON t1 BEGIN
          INSERT INTO log VALUES('before', old.a,old.b,old.c, NULL,NULL,NULL);
        END;
        CREATE TRIGGER trig6 AFTER DELETE ON t1 BEGIN
          INSERT INTO log VALUES('after', old.a,old.b,old.c, NULL,NULL,NULL);
        END;
    ]], {
        -- <triggerC-1.1>

        -- </triggerC-1.1>
    })

test:do_execsql_test(
    "triggerC-1.2",
    [[
        INSERT INTO t1 VALUES('A', 'B', 'C');
        SELECT * FROM log ORDER BY t DESC;
    ]], {
        -- <triggerC-1.2>
        "before", "", "", "", "A", "B", "C", "after", "", "", "", "A", "B", "C"
        -- </triggerC-1.2>
    })

test:do_execsql_test(
    "triggerC-1.3",
    [[
        SELECT * FROM t1
    ]], {
        -- <triggerC-1.3>
        "A", "B", "C"
        -- </triggerC-1.3>
    })

test:do_execsql_test(
    "triggerC-1.4",
    [[
        DELETE FROM log;
        UPDATE t1 SET a = 'a';
        SELECT * FROM log ORDER BY t DESC;
    ]], {
        -- <triggerC-1.4>
        "before", "A", "B", "C", "a", "B", "C", "after", "A", "B", "C", "a", "B", "C"
        -- </triggerC-1.4>
    })

test:do_execsql_test(
    "triggerC-1.5",
    [[
        SELECT * FROM t1
    ]], {
        -- <triggerC-1.5>
        "a", "B", "C"
        -- </triggerC-1.5>
    })

test:do_execsql_test(
    "triggerC-1.6",
    [[
        DELETE FROM log;
        DELETE FROM t1;
        SELECT * FROM log ORDER BY t DESC;
    ]], {
        -- <triggerC-1.6>
        "before", "a", "B", "C", "", "", "", "after", "a", "B", "C", "", "", ""
        -- </triggerC-1.6>
    })

test:do_execsql_test(
    "triggerC-1.7",
    [[
        SELECT * FROM t1
    ]], {
        -- <triggerC-1.7>

        -- </triggerC-1.7>
    })

-- MUST_WORK_TEST
test:do_execsql_test(
    "triggerC-1.8",
    [[
        CREATE TABLE t4(a PRIMARY KEY, b);
        CREATE TRIGGER t4t AFTER DELETE ON t4 BEGIN
          SELECT RAISE(ABORT, 'delete is not supported');
        END;
    ]], {
        -- <triggerC-1.8>

        -- </triggerC-1.8>
    })

test:do_test(
    "triggerC-1.9",
    function()
        test:execsql " INSERT INTO t4 VALUES(1, 2) "
        return test:catchsql " DELETE FROM t4 "
    end, {
        -- <triggerC-1.9>
        1, "delete is not supported"
        -- </triggerC-1.9>
    })

-- Tarantool: Issue submitted #2506
-- Should be uncommented as far as bug is fixed
-- test:do_execsql_test(
--     "triggerC-1.10",
--     [[
--         SELECT * FROM t4
--     ]], {
--         -- <triggerC-1.10>
--         1, 2
--         -- </triggerC-1.10>
--     })

test:do_execsql_test(
    "triggerC-1.11",
    [[
        CREATE TABLE t5 (a primary key, b, c);
        INSERT INTO t5 values (1, 2, 3);
        CREATE TRIGGER au_tbl AFTER UPDATE ON t5 BEGIN
          UPDATE OR IGNORE t5 SET a = new.a, c = 10;
        END;
    ]], {
        -- <triggerC-1.11>

        -- </triggerC-1.11>
    })

test:do_catchsql_test(
    "triggerC-1.12",
    [[
        UPDATE OR REPLACE t5 SET a = 4 WHERE a = 1
    ]], {
        -- <triggerC-1.12>
        1, "too many levels of trigger recursion"
        -- </triggerC-1.12>
    })

test:do_execsql_test(
    "triggerC-1.13",
    [[
        CREATE TABLE t6(a INTEGER PRIMARY KEY, b);
        INSERT INTO t6 VALUES(1, 2);
        create trigger r1 after update on t6 for each row begin
          SELECT 1;
        end;
        UPDATE t6 SET a=a;
    ]], {
        -- <triggerC-1.13>

        -- </triggerC-1.13>
    })

-- MUST_WORK_TEST
-- do_test triggerC-1.14 {
--   execsql {
--     DROP TABLE t1;
--     CREATE TABLE cnt(n PRIMARY KEY);
--     INSERT INTO cnt VALUES(0);
--     CREATE TABLE t1(a INTEGER PRIMARY KEY, b UNIQUE, c, d, e);
--     CREATE INDEX t1cd ON t1(c,d);
--     CREATE TRIGGER t1r1 AFTER UPDATE ON t1 BEGIN UPDATE cnt SET n=n+1; END;
--     INSERT INTO t1 VALUES(1,2,3,4,5);
--     INSERT INTO t1 VALUES(6,7,8,9,10);
--     INSERT INTO t1 VALUES(11,12,13,14,15);
--   }
-- } {}
-- do_test triggerC-1.15 {
--   catchsql { UPDATE OR ROLLBACK t1 SET a=100 }
-- } {1 {UNIQUE constraint failed: t1.a}}
---------------------------------------------------------------------------
-- This block of tests, triggerC-2.*, tests that recursive trigger
-- programs (triggers that fire themselves) work. More specifically,
-- this block focuses on recursive INSERT triggers.
--
test:do_execsql_test(
    "triggerC-2.1.0",
    [[
        CREATE TABLE t2(a PRIMARY KEY);
    ]], {
        -- <triggerC-2.1.0>

        -- </triggerC-2.1.0>
    })

-- MUST_WORK_TEST
-- for _ in X(0, "X!foreach", [=[["n tdefn rc","\n  1 {\n    CREATE TRIGGER t2_trig AFTER INSERT ON t2 WHEN (new.a>0) BEGIN\n      INSERT INTO t2 VALUES(new.a - 1);\n    END;\n  } {0 {10 9 8 7 6 5 4 3 2 1 0}}\n\n  2 {\n    CREATE TRIGGER t2_trig AFTER INSERT ON t2 BEGIN\n      SELECT CASE WHEN new.a==2 THEN RAISE(IGNORE) ELSE NULL END;\n      INSERT INTO t2 VALUES(new.a - 1);\n    END;\n  } {0 {10 9 8 7 6 5 4 3 2}}\n\n  3 {\n    CREATE TRIGGER t2_trig BEFORE INSERT ON t2 WHEN (new.a>0) BEGIN\n      INSERT INTO t2 VALUES(new.a - 1);\n    END;\n  } {0 {0 1 2 3 4 5 6 7 8 9 10}}\n\n  4 {\n    CREATE TRIGGER t2_trig BEFORE INSERT ON t2 BEGIN\n      SELECT CASE WHEN new.a==2 THEN RAISE(IGNORE) ELSE NULL END;\n      INSERT INTO t2 VALUES(new.a - 1);\n    END;\n  } {0 {3 4 5 6 7 8 9 10}}\n\n  5 {\n    CREATE TRIGGER t2_trig BEFORE INSERT ON t2 BEGIN\n      INSERT INTO t2 VALUES(new.a - 1);\n    END;\n  } {1 {too many levels of trigger recursion}}\n\n  6 {\n    CREATE TRIGGER t2_trig AFTER INSERT ON t2 WHEN (new.a>0) BEGIN\n      INSERT OR IGNORE INTO t2 VALUES(new.a);\n    END;\n  } {0 10}\n\n  7 {\n    CREATE TRIGGER t2_trig BEFORE INSERT ON t2 WHEN (new.a>0) BEGIN\n      INSERT OR IGNORE INTO t2 VALUES(new.a);\n    END;\n  } {1 {too many levels of trigger recursion}}\n"]]=]) do

local
tests =   { {[[ CREATE TRIGGER t2_trig AFTER INSERT ON t2 WHEN (new.a>0) BEGIN
                  INSERT INTO t2 VALUES(new.a - 1);
                END;]], {0, {10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0}}},

            {[[ CREATE TRIGGER t2_trig AFTER INSERT ON t2 BEGIN
                  SELECT CASE WHEN new.a==2 THEN RAISE(IGNORE) ELSE NULL END;
                  INSERT INTO t2 VALUES(new.a - 1);
                END;]], {0, {10, 9, 8, 7, 6, 5, 4, 3, 2}}},

            {[[ CREATE TRIGGER t2_trig BEFORE INSERT ON t2 WHEN (new.a>0) BEGIN
                  INSERT INTO t2 VALUES(new.a - 1);
                END;]], {0, {10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0}}},

            {[[ CREATE TRIGGER t2_trig BEFORE INSERT ON t2 BEGIN
                  SELECT CASE WHEN new.a==2 THEN RAISE(IGNORE) ELSE NULL END;
                  INSERT INTO t2 VALUES(new.a - 1);
                END;]], {0, {10, 9, 8, 7, 6, 5, 4, 3}}},

            {[[ CREATE TRIGGER t2_trig BEFORE INSERT ON t2 BEGIN
                  INSERT INTO t2 VALUES(new.a - 1);
                END;]], {1, "too many levels of trigger recursion"}},

            {[[ CREATE TRIGGER t2_trig AFTER INSERT ON t2 WHEN (new.a>0) BEGIN
                  INSERT OR IGNORE INTO t2 VALUES(new.a);
                END;]], {0, {10}}},

            {[[  CREATE TRIGGER t2_trig BEFORE INSERT ON t2 WHEN (new.a>0) BEGIN
                   INSERT OR IGNORE INTO t2 VALUES(new.a);
                 END;]], {1, "too many levels of trigger recursion"}}}

for n, v in ipairs(tests) do
    test:do_test(
        "triggerC-2.1."..n,
        function()
            test:catchsql " DROP TRIGGER t2_trig "
            test:execsql " DELETE FROM t2 "
            test:execsql(v[1])
            return test:catchsql [[
                INSERT INTO t2 VALUES(10);
                SELECT * FROM t2 ORDER BY a DESC;
            ]]
        end,
        v[2])
end

-- test:do_execsql_test(
--     "triggerC-2.2",
-- string.format([[
--         CREATE TABLE t22(x PRIMARY KEY);

--         CREATE TRIGGER t22a AFTER INSERT ON t22 BEGIN
--           INSERT INTO t22 SELECT x + (SELECT max(x) FROM t22) FROM t22;
--         END;
--         CREATE TRIGGER t22b BEFORE INSERT ON t22 BEGIN
--           SELECT CASE WHEN (SELECT count(*) FROM t22) >= %s
--                       THEN RAISE(IGNORE)
--                       ELSE NULL END;
--         END;

--         INSERT INTO t22 VALUES(1);
--         SELECT count(*) FROM t22;
--     ]], (SQLITE_MAX_TRIGGER_DEPTH / 2)), {
--         -- <triggerC-2.2>
--         (SQLITE_MAX_TRIGGER_DEPTH / 2)
--         -- </triggerC-2.2>
--     })

-- test:do_execsql_test(
--     "triggerC-2.3",
-- string.format([[
--         CREATE TABLE t23(x PRIMARY KEY);

--         CREATE TRIGGER t23a AFTER INSERT ON t23 BEGIN
--           INSERT INTO t23 VALUES(new.x + 1);
--         END;

--         CREATE TRIGGER t23b BEFORE INSERT ON t23 BEGIN
--           SELECT CASE WHEN new.x>%s
--                       THEN RAISE(IGNORE)
--                       ELSE NULL END;
--         END;

--         INSERT INTO t23 VALUES(1);
--         SELECT count(*) FROM t23;
--     ]], (SQLITE_MAX_TRIGGER_DEPTH / 2)), {
--         -- <triggerC-2.3>
--         (SQLITE_MAX_TRIGGER_DEPTH / 2)
--         -- </triggerC-2.3>
--     })

-------------------------------------------------------------------------
-- This block of tests, triggerC-3.*, test that SQLite throws an exception
-- when it detects excessive recursion.
--
test:do_execsql_test(
    "triggerC-3.1.1",
    [[
        CREATE TABLE t3(a PRIMARY KEY, b);
        CREATE TRIGGER t3i AFTER INSERT ON t3 BEGIN
          DELETE FROM t3 WHERE a = new.a;
        END;
        CREATE TRIGGER t3d AFTER DELETE ON t3 BEGIN
          INSERT INTO t3 VALUES(old.a, old.b);
        END;
    ]], {
        -- <triggerC-3.1.1>

        -- </triggerC-3.1.1>
    })

-- MUST_WORK_TEST
test:do_catchsql_test(
    "triggerC-3.1.2",
    [[
        INSERT INTO t3 VALUES(0,0)
    ]], {
        -- <triggerC-3.1.2>
        1, "too many levels of trigger recursion"
        -- </triggerC-3.1.2>
    })

-- Tarantool: Issue submitted #2506
-- Should be uncommented as far as bug is fixed
-- test:do_execsql_test(
--     "triggerC-3.1.3",
--     [[
--         SELECT * FROM t3
--     ]], {
--         -- <triggerC-3.1.3>

--         -- </triggerC-3.1.3>
--     })

-- do_test triggerC-3.2.1 {
--   execsql "
--     CREATE TABLE t3b(x);
--     CREATE TRIGGER t3bi AFTER INSERT ON t3b WHEN new.x<[expr $SQLITE_MAX_TRIGGER_DEPTH * 2] BEGIN
--       INSERT INTO t3b VALUES(new.x+1);
--     END;
--   "
--   catchsql {
--     INSERT INTO t3b VALUES(1);
--   }
-- } {1 {too many levels of trigger recursion}}
-- do_test triggerC-3.2.2 {
--   db eval {SELECT * FROM t3b}
-- } {}
-- do_test triggerC-3.3.1 {
--   catchsql "
--     INSERT INTO t3b VALUES([expr $SQLITE_MAX_TRIGGER_DEPTH + 1]);
--   "
-- } {0 {}}
-- do_test triggerC-3.3.2 {
--   db eval {SELECT count(*), max(x), min(x) FROM t3b}
-- } [list $SQLITE_MAX_TRIGGER_DEPTH [expr $SQLITE_MAX_TRIGGER_DEPTH * 2] [expr $SQLITE_MAX_TRIGGER_DEPTH + 1]]
-- do_test triggerC-3.4.1 {
--   catchsql "
--     DELETE FROM t3b;
--     INSERT INTO t3b VALUES([expr $SQLITE_MAX_TRIGGER_DEPTH - 1]);
--   "
-- } {1 {too many levels of trigger recursion}}
-- do_test triggerC-3.4.2 {
--   db eval {SELECT count(*), max(x), min(x) FROM t3b}
-- } {0 {} {}}
-- do_test triggerC-3.5.1 {
--   sqlite3_limit db SQLITE_LIMIT_TRIGGER_DEPTH  [expr $SQLITE_MAX_TRIGGER_DEPTH / 10]
--   catchsql "
--     INSERT INTO t3b VALUES([expr ($SQLITE_MAX_TRIGGER_DEPTH * 2) - ($SQLITE_MAX_TRIGGER_DEPTH / 10) + 1]);
--   "
-- } {0 {}}
-- do_test triggerC-3.5.2 {
--   db eval {SELECT count(*), max(x), min(x) FROM t3b}
-- } [list [expr $SQLITE_MAX_TRIGGER_DEPTH / 10] [expr $SQLITE_MAX_TRIGGER_DEPTH * 2] [expr ($SQLITE_MAX_TRIGGER_DEPTH * 2) - ($SQLITE_MAX_TRIGGER_DEPTH / 10) + 1]]
-- do_test triggerC-3.5.3 {
--   catchsql "
--     DELETE FROM t3b;
--     INSERT INTO t3b VALUES([expr ($SQLITE_MAX_TRIGGER_DEPTH * 2) - ($SQLITE_MAX_TRIGGER_DEPTH / 10)]);
--   "
-- } {1 {too many levels of trigger recursion}}
-- do_test triggerC-3.5.4 {
--   db eval {SELECT count(*), max(x), min(x) FROM t3b}
-- } {0 {} {}}
-- do_test triggerC-3.6.1 {
--   sqlite3_limit db SQLITE_LIMIT_TRIGGER_DEPTH 1
--   catchsql "
--     INSERT INTO t3b VALUES([expr $SQLITE_MAX_TRIGGER_DEPTH * 2]);
--   "
-- } {0 {}}
-- do_test triggerC-3.6.2 {
--   db eval {SELECT count(*), max(x), min(x) FROM t3b}
-- } [list 1 [expr $SQLITE_MAX_TRIGGER_DEPTH * 2] [expr $SQLITE_MAX_TRIGGER_DEPTH * 2]]
-- do_test triggerC-3.6.3 {
--   catchsql "
--     DELETE FROM t3b;
--     INSERT INTO t3b VALUES([expr ($SQLITE_MAX_TRIGGER_DEPTH * 2) - 1]);
--   "
-- } {1 {too many levels of trigger recursion}}
-- do_test triggerC-3.6.4 {
--   db eval {SELECT count(*), max(x), min(x) FROM t3b}
-- } {0 {} {}}
-- sqlite3_limit db SQLITE_LIMIT_TRIGGER_DEPTH $SQLITE_MAX_TRIGGER_DEPTH
-------------------------------------------------------------------------
-- This next block of tests, triggerC-4.*, checks that affinity
-- transformations and constraint processing is performed at the correct
-- times relative to BEFORE and AFTER triggers.
--
-- For an INSERT statement, for each row to be inserted:
--
--   1. Apply affinities to non-rowid values to be inserted.
--   2. Fire BEFORE triggers.
--   3. Process constraints.
--   4. Insert new record.
--   5. Fire AFTER triggers.
--
-- If the value of the rowid field is to be automatically assigned, it is
-- set to -1 in the new.* record. Even if it is explicitly set to NULL
-- by the INSERT statement.
--
-- For an UPDATE statement, for each row to be deleted:
--
--   1. Apply affinities to non-rowid values to be inserted.
--   2. Fire BEFORE triggers.
--   3. Process constraints.
--   4. Insert new record.
--   5. Fire AFTER triggers.
--
-- For a DELETE statement, for each row to be deleted:
--
--   1. Fire BEFORE triggers.
--   2. Remove database record.
--   3. Fire AFTER triggers.
--
-- When a numeric value that as an exact integer representation is stored
-- in a column with REAL affinity, it is actually stored as an integer.
-- These tests check that the typeof() such values is always 'real',
-- not 'integer'.
--
-- triggerC-4.1.*: Check that affinity transformations are made before
--                 triggers are invoked.
--
test:do_test(
    "triggerC-4.1.1",
    function()
        test:catchsql " DROP TABLE log "
        test:catchsql " DROP TABLE t4 "
        return test:execsql [[
            CREATE TABLE log(id PRIMARY KEY, t);
            CREATE TABLE t4(a TEXT PRIMARY KEY,b INTEGER,c REAL);
            CREATE TRIGGER t4bi BEFORE INSERT ON t4 BEGIN
              INSERT INTO log VALUES((SELECT coalesce(max(id),0) + 1 FROM log),
                                     new.a     || ' ' || typeof(new.a)     || ' ' ||
                                     new.b     || ' ' || typeof(new.b)     || ' ' ||
                                     new.c     || ' ' || typeof(new.c)
              );
            END;
            CREATE TRIGGER t4ai AFTER INSERT ON t4 BEGIN
              INSERT INTO log VALUES((SELECT coalesce(max(id),0) + 1 FROM log),
                                     new.a     || ' ' || typeof(new.a)     || ' ' ||
                                     new.b     || ' ' || typeof(new.b)     || ' ' ||
                                     new.c     || ' ' || typeof(new.c)
              );
            END;
            CREATE TRIGGER t4bd BEFORE DELETE ON t4 BEGIN
              INSERT INTO log VALUES((SELECT coalesce(max(id),0) + 1 FROM log),
                                     old.a     || ' ' || typeof(old.a)     || ' ' ||
                                     old.b     || ' ' || typeof(old.b)     || ' ' ||
                                     old.c     || ' ' || typeof(old.c)
              );
            END;
            CREATE TRIGGER t4ad AFTER DELETE ON t4 BEGIN
              INSERT INTO log VALUES((SELECT coalesce(max(id),0) + 1 FROM log),
                                     old.a     || ' ' || typeof(old.a)     || ' ' ||
                                     old.b     || ' ' || typeof(old.b)     || ' ' ||
                                     old.c     || ' ' || typeof(old.c)
              );
            END;
            CREATE TRIGGER t4bu BEFORE UPDATE ON t4 BEGIN
              INSERT INTO log VALUES((SELECT coalesce(max(id),0) + 1 FROM log),
                                     old.a     || ' ' || typeof(old.a)     || ' ' ||
                                     old.b     || ' ' || typeof(old.b)     || ' ' ||
                                     old.c     || ' ' || typeof(old.c)
              );
              INSERT INTO log VALUES((SELECT coalesce(max(id),0) + 1 FROM log),
                                     new.a     || ' ' || typeof(new.a)     || ' ' ||
                                     new.b     || ' ' || typeof(new.b)     || ' ' ||
                                     new.c     || ' ' || typeof(new.c)
              );
            END;
            CREATE TRIGGER t4au AFTER UPDATE ON t4 BEGIN
              INSERT INTO log VALUES((SELECT coalesce(max(id),0) + 1 FROM log),
                                     old.a     || ' ' || typeof(old.a)     || ' ' ||
                                     old.b     || ' ' || typeof(old.b)     || ' ' ||
                                     old.c     || ' ' || typeof(old.c)
              );
              INSERT INTO log VALUES((SELECT coalesce(max(id),0) + 1 FROM log),
                                     new.a     || ' ' || typeof(new.a)     || ' ' ||
                                     new.b     || ' ' || typeof(new.b)     || ' ' ||
                                     new.c     || ' ' || typeof(new.c)
              );
            END;
        ]]
    end, {
        -- <triggerC-4.1.1>

        -- </triggerC-4.1.1>
    })

local
tests4 = {{ [[INSERT INTO t4 VALUES('1', '1', '1');
              DELETE FROM t4;]], {
                 "1 text 1 integer 1.0 real",
                 "1 text 1 integer 1.0 real",
                 "1 text 1 integer 1.0 real",
                 "1 text 1 integer 1.0 real"}},

          { [[INSERT INTO t4(a,b,c) VALUES(45, 45, 45);
              DELETE FROM t4;]], {
                  "45 text 45 integer 45.0 real",
                  "45 text 45 integer 45.0 real",
                  "45 text 45 integer 45.0 real",
                  "45 text 45 integer 45.0 real"}},

          { [[INSERT INTO t4(a,b,c) VALUES(-42.0, -42.0, -42.0);
              DELETE FROM t4;]], {
                  "-42.0 text -42 integer -42.0 real",
                  "-42.0 text -42 integer -42.0 real",
                  "-42.0 text -42 integer -42.0 real",
                  "-42.0 text -42 integer -42.0 real"}},

          { [[INSERT INTO t4(a,b,c) VALUES(-42.4, -42.4, -42.4);
              DELETE FROM t4;]], {
                  "-42.4 text -42.4 real -42.4 real",
                  "-42.4 text -42.4 real -42.4 real",
                  "-42.4 text -42.4 real -42.4 real",
                  "-42.4 text -42.4 real -42.4 real"}},

          { [[INSERT INTO t4 VALUES(7, 7, 7);
              UPDATE t4 SET a=8, b=8, c=8;]], {
                  "7 text 7 integer 7.0 real",
                  "7 text 7 integer 7.0 real",
                  "7 text 7 integer 7.0 real",
                  "8 text 8 integer 8.0 real",
                  "7 text 7 integer 7.0 real",
                  "8 text 8 integer 8.0 real"}},

          { [[UPDATE t4 SET a=8;]], {
                  "8 text 8 integer 8.0 real",
                  "8 text 8 integer 8.0 real",
                  "8 text 8 integer 8.0 real",
                  "8 text 8 integer 8.0 real"}},

          { [[UPDATE t4 SET a='9', b='9', c='9';]], {
                  "8 text 8 integer 8.0 real",
                  "9 text 9 integer 9.0 real",
                  "8 text 8 integer 8.0 real",
                  "9 text 9 integer 9.0 real"}},

          { [[UPDATE t4 SET a='9.1', b='9.1', c='9.1';]], {
                  "9 text 9 integer 9.0 real",
                  "9.1 text 9.1 real 9.1 real",
                  "9 text 9 integer 9.0 real",
                  "9.1 text 9.1 real 9.1 real"}}}

              -- MUST_WORK_TEST
-- for _ in X(0, "X!foreach", [=[["n insert log","\n\n  2 {\n   INSERT INTO t4 VALUES('1', '1', '1');\n   DELETE FROM t4;\n  } {\n     1 integer 1 text 1 integer 1.0 real\n     1 integer 1 text 1 integer 1.0 real\n     1 integer 1 text 1 integer 1.0 real\n  }\n\n  3 {\n   INSERT INTO t4(a,b,c) VALUES(45, 45, 45);\n   DELETE FROM t4;\n  } {\n    45 integer 45 text 45 integer 45.0 real\n    45 integer 45 text 45 integer 45.0 real\n    45 integer 45 text 45 integer 45.0 real\n  }\n\n  4 {\n   INSERT INTO t4(a,b,c) VALUES(-42.0, -42.0, -42.0);\n   DELETE FROM t4;\n  } {\n    -42 integer -42.0 text -42 integer -42.0 real\n    -42 integer -42.0 text -42 integer -42.0 real\n    -42 integer -42.0 text -42 integer -42.0 real\n  }\n\n  5 {\n   INSERT INTO t4(a,b,c) VALUES(-42.4, -42.4, -42.4);\n   DELETE FROM t4;\n  } {\n     1 integer -42.4 text -42.4 real -42.4 real\n     1 integer -42.4 text -42.4 real -42.4 real\n     1 integer -42.4 text -42.4 real -42.4 real\n  }\n\n  6 {\n   INSERT INTO t4 VALUES(7, 7, 7);\n   UPDATE t4 SET a=8, b=8, c=8;\n  } {\n    -1 integer 7 text 7 integer 7.0 real\n     1 integer 7 text 7 integer 7.0 real\n     1 integer 7 text 7 integer 7.0 real\n     1 integer 8 text 8 integer 8.0 real\n     1 integer 7 text 7 integer 7.0 real\n     1 integer 8 text 8 integer 8.0 real\n  }\n\n  8 {\n   UPDATE t4 SET a='9', b='9', c='9';\n  } {\n     2 integer 9 text 9 integer 9.0 real\n     2 integer 8 text 8 integer 8.0 real\n     2 integer 9 text 9 integer 9.0 real\n  }\n\n  9 {\n   UPDATE t4 SET a='9.1', b='9.1', c='9.1';\n  } {\n     2 integer 9.1 text 9.1 real    9.1 real\n     2 integer 9   text 9   integer 9.0 real\n     2 integer 9.1 text 9.1 real    9.1 real\n  }\n"]]=]) do

for n, v in ipairs(tests4) do
    test:do_execsql_test(
        "triggerC-4.1."..(n+1),
        string.format([[ DELETE FROM log;
                         %s ;
                         SELECT t FROM log ORDER BY id;]], v[1]),
        v[2])
end
---------------------------------------------------------------------------
-- This block of tests, triggerC-5.*, test that DELETE triggers are fired
-- if a row is deleted as a result of OR REPLACE conflict resolution.
--
test:do_execsql_test(
    "triggerC-5.1.0",
    [[
        DROP TABLE IF EXISTS t5;
        CREATE TABLE t5(a INTEGER PRIMARY KEY, b);
        CREATE UNIQUE INDEX t5i ON t5(b);
        INSERT INTO t5 VALUES(1, 'a');
        INSERT INTO t5 VALUES(2, 'b');
        INSERT INTO t5 VALUES(3, 'c');

        CREATE TABLE t5g(a PRIMARY KEY, b, c);
        CREATE TRIGGER t5t BEFORE DELETE ON t5 BEGIN
          INSERT INTO t5g VALUES(old.a, old.b, (SELECT count(*) FROM t5));
        END;
    ]], {
        -- <triggerC-5.1.0>

        -- </triggerC-5.1.0>
    })

-- MUST_WORK_TEST
-- foreach {n dml t5g t5} {
--   1 "DELETE FROM t5 WHERE a=2"                        {2 b 3} {1 a 3 c}
--   2 "INSERT OR REPLACE INTO t5 VALUES(2, 'd')"        {2 b 3} {1 a 2 d 3 c}
--   3 "UPDATE OR REPLACE t5 SET a = 2 WHERE a = 3"      {2 b 3} {1 a 2 c}
--   4 "INSERT OR REPLACE INTO t5 VALUES(4, 'b')"        {2 b 3} {1 a 3 c 4 b}
--   5 "UPDATE OR REPLACE t5 SET b = 'b' WHERE b = 'c'"  {2 b 3} {1 a 3 b}
--   6 "INSERT OR REPLACE INTO t5 VALUES(2, 'c')"        {2 b 3 3 c 2} {1 a 2 c}
--   7 "UPDATE OR REPLACE t5 SET a=1, b='b' WHERE a = 3" {1 a 3 2 b 2} {1 b}
-- } {
--   do_test triggerC-5.1.$n {
--     execsql "
--       BEGIN;
--         $dml ;
--         SELECT * FROM t5g ORDER BY rowid;
--         SELECT * FROM t5 ORDER BY rowid;
--       ROLLBACK;
--     "
--   } [concat $t5g $t5]
-- }
test:do_execsql_test(
    "triggerC-5.2.0",
    [[
        DROP TRIGGER t5t;
        CREATE TRIGGER t5t AFTER DELETE ON t5 BEGIN
          INSERT INTO t5g VALUES(old.a, old.b, (SELECT count(*) FROM t5));
        END;
    ]], {
        -- <triggerC-5.2.0>

        -- </triggerC-5.2.0>
    })

-- MUST_WORK_TEST
-- foreach {n dml t5g t5} {
--   1 "DELETE FROM t5 WHERE a=2"                        {2 b 2} {1 a 3 c}
--   2 "INSERT OR REPLACE INTO t5 VALUES(2, 'd')"        {2 b 2} {1 a 2 d 3 c}
--   3 "UPDATE OR REPLACE t5 SET a = 2 WHERE a = 3"      {2 b 2} {1 a 2 c}
--   4 "INSERT OR REPLACE INTO t5 VALUES(4, 'b')"        {2 b 2} {1 a 3 c 4 b}
--   5 "UPDATE OR REPLACE t5 SET b = 'b' WHERE b = 'c'"  {2 b 2} {1 a 3 b}
--   6 "INSERT OR REPLACE INTO t5 VALUES(2, 'c')"        {2 b 2 3 c 1} {1 a 2 c}
--   7 "UPDATE OR REPLACE t5 SET a=1, b='b' WHERE a = 3" {1 a 2 2 b 1} {1 b}
-- } {
--   do_test triggerC-5.2.$n {
--     execsql "
--       BEGIN;
--         $dml ;
--         SELECT * FROM t5g ORDER BY rowid;
--         SELECT * FROM t5 ORDER BY rowid;
--       ROLLBACK;
--     "
--   } [concat $t5g $t5]
-- }
test:do_execsql_test(
    "triggerC-5.3.0",
    [[
        PRAGMA recursive_triggers = off
    ]], {
        -- <triggerC-5.3.0>

        -- </triggerC-5.3.0>
    })

-- MUST_WORK_TEST
-- foreach {n dml t5g t5} {
--   1 "DELETE FROM t5 WHERE a=2"                        {2 b 2} {1 a 3 c}
--   2 "INSERT OR REPLACE INTO t5 VALUES(2, 'd')"        {} {1 a 2 d 3 c}
--   3 "UPDATE OR REPLACE t5 SET a = 2 WHERE a = 3"      {} {1 a 2 c}
--   4 "INSERT OR REPLACE INTO t5 VALUES(4, 'b')"        {} {1 a 3 c 4 b}
--   5 "UPDATE OR REPLACE t5 SET b = 'b' WHERE b = 'c'"  {} {1 a 3 b}
--   6 "INSERT OR REPLACE INTO t5 VALUES(2, 'c')"        {} {1 a 2 c}
--   7 "UPDATE OR REPLACE t5 SET a=1, b='b' WHERE a = 3" {} {1 b}
-- } {
--   do_test triggerC-5.3.$n {
--     execsql "
--       BEGIN;
--         $dml ;
--         SELECT * FROM t5g ORDER BY rowid;
--         SELECT * FROM t5 ORDER BY rowid;
--       ROLLBACK;
--     "
--   } [concat $t5g $t5]
-- }
test:do_execsql_test(
    "triggerC-5.3.8",
    [[
        PRAGMA recursive_triggers = on
    ]], {
        -- <triggerC-5.3.8>

        -- </triggerC-5.3.8>
    })

---------------------------------------------------------------------------
-- This block of tests, triggerC-6.*, tests that "PRAGMA recursive_triggers"
-- statements return the current value of the recursive triggers flag.
--
test:do_execsql_test(
    "triggerC-6.1",
    [[
        PRAGMA recursive_triggers
    ]], {
        -- <triggerC-6.1>
        1
        -- </triggerC-6.1>
    })

test:do_execsql_test(
    "triggerC-6.2",
    [[
        PRAGMA recursive_triggers = off;
        PRAGMA recursive_triggers;
    ]], {
        -- <triggerC-6.2>
        0
        -- </triggerC-6.2>
    })

test:do_execsql_test(
    "triggerC-6.3",
    [[
        PRAGMA recursive_triggers = on;
        PRAGMA recursive_triggers;
    ]], {
        -- <triggerC-6.3>
        1
        -- </triggerC-6.3>
    })

-- MUST_WORK_TEST
-- #-------------------------------------------------------------------------
-- # Test some of the "undefined behaviour" associated with triggers. The
-- # undefined behaviour occurs when a row being updated or deleted is
-- # manipulated by a BEFORE trigger.
-- #
-- do_test triggerC-7.1 {
--   execsql {
--     CREATE TABLE t8(x);
--     CREATE TABLE t7(a, b);
--     INSERT INTO t7 VALUES(1, 2);
--     INSERT INTO t7 VALUES(3, 4);
--     INSERT INTO t7 VALUES(5, 6);
--     CREATE TRIGGER t7t BEFORE UPDATE ON t7 BEGIN
--       DELETE FROM t7 WHERE a = 1;
--     END;
--     CREATE TRIGGER t7ta AFTER UPDATE ON t7 BEGIN
--       INSERT INTO t8 VALUES('after fired ' || old.rowid || '->' || new.rowid);
--     END;
--   }
-- } {}
-- do_test triggerC-7.2 {
--   execsql {
--     BEGIN;
--       UPDATE t7 SET b=7 WHERE a = 5;
--       SELECT * FROM t7;
--       SELECT * FROM t8;
--     ROLLBACK;
--   }
-- } {3 4 5 7 {after fired 3->3}}
-- do_test triggerC-7.3 {
--   execsql {
--     BEGIN;
--       UPDATE t7 SET b=7 WHERE a = 1;
--       SELECT * FROM t7;
--       SELECT * FROM t8;
--     ROLLBACK;
--   }
-- } {3 4 5 6}
-- do_test triggerC-7.4 {
--   execsql {
--     DROP TRIGGER t7t;
--     CREATE TRIGGER t7t BEFORE UPDATE ON t7 WHEN (old.rowid!=1 OR new.rowid!=8)
--     BEGIN
--       UPDATE t7 set rowid = 8 WHERE rowid=1;
--     END;
--   }
-- } {}
-- do_test triggerC-7.5 {
--   execsql {
--     BEGIN;
--       UPDATE t7 SET b=7 WHERE a = 5;
--       SELECT rowid, * FROM t7;
--       SELECT * FROM t8;
--     ROLLBACK;
--   }
-- } {2 3 4 3 5 7 8 1 2 {after fired 1->8} {after fired 3->3}}
-- do_test triggerC-7.6 {
--   execsql {
--     BEGIN;
--       UPDATE t7 SET b=7 WHERE a = 1;
--       SELECT rowid, * FROM t7;
--       SELECT * FROM t8;
--     ROLLBACK;
--   }
-- } {2 3 4 3 5 6 8 1 2 {after fired 1->8}}
-- do_test triggerC-7.7 {
--   execsql {
--     DROP TRIGGER t7t;
--     DROP TRIGGER t7ta;
--     CREATE TRIGGER t7t BEFORE DELETE ON t7 BEGIN
--       UPDATE t7 set rowid = 8 WHERE rowid=1;
--     END;
--     CREATE TRIGGER t7ta AFTER DELETE ON t7 BEGIN
--       INSERT INTO t8 VALUES('after fired ' || old.rowid);
--     END;
--   }
-- } {}
-- do_test triggerC-7.8 {
--   execsql {
--     BEGIN;
--       DELETE FROM t7 WHERE a = 3;
--       SELECT rowid, * FROM t7;
--       SELECT * FROM t8;
--     ROLLBACK;
--   }
-- } {3 5 6 8 1 2 {after fired 2}}
-- do_test triggerC-7.9 {
--   execsql {
--     BEGIN;
--       DELETE FROM t7 WHERE a = 1;
--       SELECT rowid, * FROM t7;
--       SELECT * FROM t8;
--     ROLLBACK;
--   }
-- } {2 3 4 3 5 6 8 1 2}
-- # Ticket [e25d9ea771febc9c311928c1c01c3163dcb26643]
-- #
-- do_test triggerC-9.1 {
--   execsql {
--     CREATE TABLE t9(a,b);
--     CREATE INDEX t9b ON t9(b);
--     INSERT INTO t9 VALUES(1,0);
--     INSERT INTO t9 VALUES(2,1);
--     INSERT INTO t9 VALUES(3,2);
--     INSERT INTO t9 SELECT a+3, a+2 FROM t9;
--     INSERT INTO t9 SELECT a+6, a+5 FROM t9;
--     SELECT a FROM t9 ORDER BY a;
--   }
-- } {1 2 3 4 5 6 7 8 9 10 11 12}
-- do_test triggerC-9.2 {
--   execsql {
--     CREATE TRIGGER t9r1 AFTER DELETE ON t9 BEGIN
--       DELETE FROM t9 WHERE b=old.a;
--     END;
--     DELETE FROM t9 WHERE b=4;
--     SELECT a FROM t9 ORDER BY a;
--   }
-- } {1 2 3 4}
-- At one point (between versions 3.6.18 and 3.6.20 inclusive), an UPDATE
-- that fired a BEFORE trigger that itself updated the same row as the
-- statement causing it to fire was causing a strange side-effect: The
-- values updated by the statement within the trigger were being overwritten
-- by the values in the new.* array, even if those values were not
-- themselves written by the parent UPDATE statement.
--
-- Technically speaking this was not a bug. The SQLite documentation says
-- that if a BEFORE UPDATE or BEFORE DELETE trigger modifies or deletes the
-- row that the parent statement is operating on the results are undefined.
-- But as of 3.6.21 behaviour is restored to the way it was in versions
-- 3.6.17 and earlier to avoid causing unnecessary difficulties.
--
test:do_test(
    "triggerC-10.1",
    function()
        test:execsql [[
            CREATE TABLE t10(a PRIMARY KEY, updatecnt DEFAULT 0);
            CREATE TRIGGER t10_bu BEFORE UPDATE OF a ON t10 BEGIN
              UPDATE t10 SET updatecnt = updatecnt+1 WHERE a = old.a;
            END;
            INSERT INTO t10 VALUES('hello', 0);
        ]]
        -- Before the problem was fixed, table t10 would contain the tuple
        -- (world, 0) after running the following script (because the value
        -- 1 written to column "updatecnt" was clobbered by the old value 0).
        --
        return test:execsql [[
            UPDATE t10 SET a = 'world';
            SELECT * FROM t10;
        ]]
    end, {
        -- <triggerC-10.1>
        "world", 1
        -- </triggerC-10.1>
    })

test:do_execsql_test(
    "triggerC-10.2",
    [[
        UPDATE t10 SET a = 'tcl', updatecnt = 5;
        SELECT * FROM t10;
    ]], {
        -- <triggerC-10.2>
        "tcl", 5
        -- </triggerC-10.2>
    })

test:do_test(
    "triggerC-10.3",
    function()
        test:execsql [[
            CREATE TABLE t11(
              c1 PRIMARY KEY,   c2,  c3,  c4,  c5,  c6,  c7,  c8,  c9, c10,
              c11, c12, c13, c14, c15, c16, c17, c18, c19, c20,
              c21, c22, c23, c24, c25, c26, c27, c28, c29, c30,
              c31, c32, c33, c34, c35, c36, c37, c38, c39, c40
            );

            CREATE TRIGGER t11_bu BEFORE UPDATE OF c1 ON t11 BEGIN
              UPDATE t11 SET c31 = c31+1, c32=c32+1 WHERE c2 = old.c2;
            END;

            INSERT INTO t11 VALUES(
              1,   2,  3,  4,  5,  6,  7,  8,  9, 10,
              11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
              21, 22, 23, 24, 25, 26, 27, 28, 29, 30,
              31, 32, 33, 34, 35, 36, 37, 38, 39, 40
            );
        ]]
        -- Before the problem was fixed, table t10 would contain the tuple
        -- (world, 0) after running the following script (because the value
        -- 1 written to column "updatecnt" was clobbered by the old value 0).
        --
        return test:execsql [[
            UPDATE t11 SET c4=35, c33=22, c1=5;
            SELECT * FROM t11;
        ]]
    end, {
        -- <triggerC-10.3>
        5, 2, 3, 35, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 22, 34, 35, 36, 37, 38, 39, 40
        -- </triggerC-10.3>
    })

-- #-------------------------------------------------------------------------
-- # Test that bug [371bab5d65] has been fixed. BEFORE INSERT and INSTEAD OF
-- # INSERT triggers with the DEFAULT VALUES INSERT syntax.
-- #
test:do_test(
    "triggerC-11.0",
    function()
        test:catchsql " DROP TABLE IF EXISTS log "
        return test:execsql " CREATE TABLE log(id INTEGER PRIMARY KEY, a, b) "
    end, {
        -- <triggerC-11.0>

        -- </triggerC-11.0>
    })

-- MUST_WORK_TEST
local
tests11 = {-- {"CREATE TABLE t1(a PRIMARY KEY, b)",                         {{}, {}}},
           {"CREATE TABLE t1(a PRIMARY KEY DEFAULT 1, b DEFAULT 'abc')", {1, "abc"}},
           {"CREATE TABLE t1(a, b PRIMARY KEY DEFAULT 4.5)",             {"", 4.5}}}

--for _ in X(0, "X!foreach", [=[["testno tbl defaults","\n  1 \"CREATE TABLE t1(a PRIMARY KEY, b)\"                          {{} {}}\n  2 \"CREATE TABLE t1(a PRIMARY KEY DEFAULT 1, b DEFAULT 'abc')\"  {1 abc}\n  3 \"CREATE TABLE t1(a PRIMARY KEY, b DEFAULT 4.5)\"              {{} 4.5}\n"]]=]) do
for testno, v in ipairs(tests11) do
    test:do_test(
        "triggerC-11."..testno..".1",
        function()
            test:catchsql " DROP TABLE t1 "
            test:execsql " DELETE FROM log "
            test:execsql(v[1])
            return test:execsql [[
                CREATE TRIGGER tt1 BEFORE INSERT ON t1 BEGIN
                  INSERT INTO log VALUES((SELECT coalesce(max(id),0) + 1 FROM log),
                                         new.a, new.b);
                END;
                INSERT INTO t1 DEFAULT VALUES;
                SELECT a,b FROM log;
            ]]
        end, v[2])

    -- Tarantool: we're unable to do double insert of default vals
    -- (PK will be not unique). Comment so far
    -- test:do_test(
    --     "triggerC-11."..testno..".2",
    --     function()
    --         test:execsql " DELETE FROM log "
    --         return test:execsql [[
    --             CREATE TRIGGER tt2 AFTER INSERT ON t1 BEGIN
    --               INSERT INTO log VALUES(new.a, new.b);
    --             END;
    --             INSERT INTO t1 DEFAULT VALUES;
    --             SELECT * FROM log;
    --         ]]
    --     end, {
    --         -- X(891, "X!cmd", [=[["concat",["defaults"],["defaults"]]]=])
    --     })

    test:do_test(
        "triggerC-11."..testno..".3",
        function()
            test:execsql " DROP TRIGGER tt1 "
            test:execsql " DELETE FROM t1"
            test:execsql " DELETE FROM log "
            return test:execsql [[
                INSERT INTO t1 DEFAULT VALUES;
                SELECT a,b FROM log;
            ]]
        end, {
            defaults
        })

    --
end
test:do_test(
    "triggerC-11.4",
    function()
        test:catchsql " DROP TABLE t2 "
        return test:execsql [[
            DELETE FROM log;
            CREATE TABLE t2(a PRIMARY KEY, b);
            CREATE VIEW v2 AS SELECT * FROM t2;
            CREATE TRIGGER tv2 INSTEAD OF INSERT ON v2 BEGIN
              INSERT INTO log VALUES((SELECT coalesce(max(id),0) + 1 FROM log),
                                     new.a, new.b);
            END;
            INSERT INTO v2 DEFAULT VALUES;
            SELECT a, b, a IS NULL, b IS NULL FROM log;
        ]]
    end, {
        -- <triggerC-11.4>
        "", "", 1, 1
        -- </triggerC-11.4>
    })

-- do_test triggerC-12.1 {
--   db close
--   forcedelete test.db
--   sqlite3 db test.db
test:execsql(
    [[
    DROP TABLE t1;
    CREATE TABLE t1(id INTEGER PRIMARY KEY, a, b);
    INSERT INTO t1 VALUES(1, 1, 2);
    INSERT INTO t1 VALUES(2, 3, 4);
    INSERT INTO t1 VALUES(3, 5, 6);
    CREATE TRIGGER tr1 AFTER INSERT ON t1 BEGIN SELECT 1 ; END ;]])

test:do_execsql_test(
    "triggerC-13.1",
    [[
        PRAGMA recursive_triggers = ON;
        CREATE TABLE t12(id INTEGER PRIMARY KEY, a, b);
        INSERT INTO t12 VALUES(1, 1, 2);
        CREATE TRIGGER tr12 AFTER UPDATE ON t12 BEGIN
          UPDATE t12 SET a=new.a+1, b=new.b+1;
        END;
    ]], {
        -- <triggerC-13.1>

        -- </triggerC-13.1>
    })

test:do_catchsql_test(
    "triggerC-13.2",
    [[
        UPDATE t12 SET a=a+1, b=b+1;
    ]], {
        -- <triggerC-13.2>
        1, "too many levels of trigger recursion"
        -- </triggerC-13.2>
    })

---------------------------------------------------------------------------
-- The following tests seek to verify that constant values (i.e. literals)
-- are not factored out of loops within trigger programs. SQLite does
-- not factor constants out of loops within trigger programs as it may only
-- do so in code generated before the first table or index is opened. And
-- by the time a trigger program is coded, at least one table or index has
-- always been opened.
--
-- At one point, due to a bug allowing constant factoring within triggers,
-- the following SQL would produce the wrong result.
--
SQL = [[
  DROP TABLE IF EXISTS t1;
  DROP TABLE IF EXISTS t2;
  DROP TABLE IF EXISTS t4;
  DROP TABLE IF EXISTS t5;
  CREATE TABLE t1(a PRIMARY KEY, b, c);
  CREATE INDEX i1 ON t1(a, c);
  CREATE INDEX i2 ON t1(b, c);
  INSERT INTO t1 VALUES(1, 2, 3);

  CREATE TABLE t2(e PRIMARY KEY, f);
  CREATE INDEX i3 ON t2(e);
  INSERT INTO t2 VALUES(1234567, 3);

  CREATE TABLE empty(x PRIMARY KEY);
  CREATE TABLE not_empty(x PRIMARY KEY);
  INSERT INTO not_empty VALUES(2);

  CREATE TABLE t4(x PRIMARY KEY);
  CREATE TABLE t5(g PRIMARY KEY, h, i);

  CREATE TRIGGER trig BEFORE INSERT ON t4 BEGIN
    INSERT INTO t5 SELECT * FROM t1 WHERE
        (a IN (SELECT x FROM empty) OR b IN (SELECT x FROM not_empty))
        AND c IN (SELECT f FROM t2 WHERE e=1234567);
  END;

  INSERT INTO t4 VALUES(0);
  SELECT * FROM t5;
]]
-- reset_db
test:do_execsql_test(
    "triggerC-14.1",
    SQL, {
        -- <triggerC-14.1>
        1, 2, 3
        -- </triggerC-14.1>
    })

-- reset_db
-- optimization_control db factor-constants 0
-- do_execsql_test triggerC-14.2 $SQL {1 2 3}
-- MUST_WORK_TEST
---------------------------------------------------------------------------
-- Check that table names used by trigger programs are dequoted exactly
-- once.
--
test:do_execsql_test(
    "triggerC-15.1.1",
    [[
        PRAGMA recursive_triggers = 1;
        CREATE TABLE node(
            id int not null primary key,
            pid int not null default 0 references node,
            key varchar not null,
            path varchar default '',
            unique(pid, key)
            );
        CREATE TRIGGER node_delete_referencing AFTER DELETE ON "node"
          BEGIN
          DELETE FROM "node" WHERE pid = old."id";
        END;
    ]])

test:do_execsql_test(
    "triggerC-15.1.2",
    [[
        INSERT INTO node(id, pid, key) VALUES(9, 0, 'test');
        INSERT INTO node(id, pid, key) VALUES(90, 9, 'test1');
        INSERT INTO node(id, pid, key) VALUES(900, 90, 'test2');
        DELETE FROM node WHERE id=9;
        SELECT * FROM node;
    ]])

-- Tarantool: such indentifiers are not working
-- Comment so far
-- test:do_execsql_test(
--     "15.2.1",
--     [[
--         CREATE TABLE   x1  (x PRIMARY KEY);

--         CREATE TABLE '"x2"'(a PRIMARY KEY, b);

--         INSERT INTO x2 VALUES(1, 2);
--         INSERT INTO x2 VALUES(3, 4);
--         INSERT INTO '"x2"' SELECT * FROM x2;

--         CREATE TRIGGER x1ai AFTER INSERT ON x1 BEGIN
--           INSERT INTO """x2""" VALUES('x', 'y');
--           DELETE FROM """x2""" WHERE a=1;
--           UPDATE """x2""" SET b = 11 WHERE a = 3;
--         END;

--         INSERT INTO x1 VALUES('go!');
--     ]])

-- test:do_execsql_test(
--     "15.2.2",
--     [[
--         SELECT * FROM x2;
--     ]], {
--         -- <15.2.2>
--         1, 2, 3, 4
--         -- </15.2.2>
--     })

-- test:do_execsql_test(
--     "15.2.3",
--     [[
--         SELECT * FROM """x2""";
--     ]], {
--         -- <15.2.3>
--         3, 11, "x", "y"
--         -- </15.2.3>
--     })

test:finish_test()
