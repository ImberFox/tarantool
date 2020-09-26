-- Make sure that INTEGER is not converted to DOUBLE in cases below.
box.execute("CREATE TABLE t (i NUMBER PRIMARY KEY, n NUMBER);")
box.execute("CREATE TRIGGER t AFTER INSERT ON t FOR EACH ROW BEGIN UPDATE t SET n = new.n; END;")
box.execute("INSERT INTO t VALUES (1, 1);")
box.execute("SELECT i / 2, n / 2 FROM t;")
box.execute("DROP TABLE t;")

box.execute("CREATE TABLE t (i NUMBER PRIMARY KEY, n NUMBER);")
box.execute("INSERT INTO t VALUES (1,1);")
box.execute("SELECT i / 2, n / 2 FROM t GROUP BY n;")
box.execute("DROP TABLE t;")
