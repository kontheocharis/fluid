stack run -- -c ./start.fluid

stack run -- -r ./start.fluid -n add-index -a 'data=Expr, type=`List V`, index=0' > step1.fluid
stack run -- -c ./step1.fluid

stack run -- -r ./step1.fluid -n unify-inds -a 'data=Expr, ctor=Add, indsToUnify=[5,3,1]' > step2a.fluid
stack run -- -c ./step2a.fluid

stack run -- -r ./step2a.fluid -n rel-ctor-params -a 'data=Expr, ctor=Var, inds=[2,1], reln=`Elem`' > step2b.fluid
stack run -- -c ./step2b.fluid

stack run -- -r ./step2b.fluid -n add-param -a 'func=lookupVar, index=0, type=`List V`' > step3a.fluid
stack run -- -c ./step3a.fluid

# Broken: RelFuncParams duplicates holes in recursive call
# stack run -- -r ./step3a.fluid -n rel-func-params -a 'func=lookupVar, inds=[2,3], reln=`Elem`' > step3b.fluid
stack run -- -c ./step3b.fluid

# Broken: pattern expansion
# Does not typecheck because of impossible cases (intended)
# stack run -- -c ./step3c.fluid

stack run -- -r ./step3c.fluid -n identify-impossibles -a 'decl=lookupVar' > step3d.fluid
stack run -- -c ./step3d.fluid

stack run -- -r ./step3c.fluid -n identify-impossibles -a 'decl=lookupVar' > step3d.fluid
stack run -- -c ./step3d.fluid

# Manual: fill holes
stack run -- -c ./step4.fluid

stack run -- -r ./step4.fluid -n add-param -a 'func=eval, index=0, type=`List Nat`' > step5a.fluid
stack run -- -c ./step5a.fluid

# Broken: does not add recursive holes
# stack run -- -r ./step5a.fluid -n rel-func-params -a 'func=eval, inds=[3,2,4], reln=`Unzip`' > step5b.fluid
stack run -- -c ./step5b.fluid

# Broken: pattern expansion
# Does not typecheck because of impossible cases (intended)
stack run -- -c ./step5c.fluid

# Temporary to check bool tautology removal:
stack run -- -r ./boolean-tautology.fluid -n rm-taut -a 'lx=35, ly=64, op=isEqual' > boolean-tautology2.fluid
stack run -- -c ./boolean-tautology2.fluid
