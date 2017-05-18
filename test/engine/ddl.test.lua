test_run = require('test_run')
inspector = test_run.new()
engine = inspector:get_cfg('engine')

-- space create/drop
space = box.schema.space.create('test', { engine = engine })
space:drop()


-- space index create/drop
space = box.schema.space.create('test', { engine = engine })
index = space:create_index('primary')
space:drop()


-- space index create/drop alter
space = box.schema.space.create('test', { engine = engine })
index = space:create_index('primary')
_index = box.space[box.schema.INDEX_ID]
_index:delete{102, 0}
space:drop()


-- space index create/drop tree string
space = box.schema.space.create('test', { engine = engine })
index = space:create_index('primary', {type = 'tree', parts = {1, 'string'}})
space:insert({'test'})
space:drop()


-- space index create/drop tree num
space = box.schema.space.create('test', { engine = engine })
index = space:create_index('primary', {type = 'tree', parts = {1, 'unsigned'}})
space:insert({13})
space:drop()


-- space index create/drop tree multi-part num
space = box.schema.space.create('test', { engine = engine })
index = space:create_index('primary', {type = 'tree', parts = {1, 'unsigned', 2, 'unsigned'}})
space:insert({13})
space:drop()


-- space index size
space = box.schema.space.create('test', { engine = engine })
index = space:create_index('primary')
primary = space.index[0]
primary:count()
space:insert({13})
space:insert({14})
space:insert({15})
primary:count()
space:drop()

-- Key part max
parts = {}
for i=1,box.schema.INDEX_PART_MAX,1 do parts[2 * i - 1] = i; parts[2 * i] = 'unsigned' end
space = box.schema.space.create('test', { engine = engine })
_ = space:create_index('primary', { type = 'tree', parts = parts })

tuple = {}
for i=1,box.schema.INDEX_PART_MAX,1 do tuple[i] = i; end
space:replace(tuple)
-- https://github.com/tarantool/tarantool/issues/1651 and https://github.com/tarantool/tarantool/issues/1671
-- space:upsert(tuple, {{'=', box.schema.INDEX_PART_MAX + 1, 100500}})
space:get(tuple)
space:select(tuple)
_ = space:delete(tuple)

space:drop()

-- Too many key parts
parts = {}
for i=1,box.schema.INDEX_PART_MAX + 1,1 do parts[2 * i - 1] = i; parts[2 * i] = 'unsigned' end
space = box.schema.space.create('test', { engine = engine })
_ = space:create_index('primary', { type = 'tree', parts = parts })
space:drop()

--
-- vy_mem of primary index contains statements with two formats.
--
space = box.schema.space.create('test1', { engine = engine })
pk = space:create_index('primary1')
idx2 = space:create_index('idx2', { parts = {2, 'unsigned'} })
space:replace({3, 8, 1})
idx2:select{}
space:get{3}
iter_obj = space:pairs(2, {iterator = 'GT'})
idx2:drop()
space:replace({4, 5, 6})
space:select{}
space:drop()

-- Change index name
space = box.schema.space.create('test', {engine = engine})
pk = space:create_index('pk')
space:replace{1}
space:replace{2}
space:replace{3}
box.space._index:select{space.id}[1][3]
pk:alter({name = 'altered_pk'})
box.space._index:select{space.id}[1][3]
space:drop()
