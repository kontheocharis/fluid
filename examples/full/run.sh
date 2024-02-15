stack run -- -c ./start.fluid

echo "Step 1"
stack run -- -r ./start.fluid -n add-index -a 'data=Expr, type=`List V`, index=0, name=vars' > step1.fluid
stack run -- -c ./step1.fluid

echo "Step 2a"
stack run -- -r ./step1.fluid -n unify-inds -a 'data=Expr, ctor=Add, indsToUnify=[5,3,1]' > step2a.fluid
stack run -- -c ./step2a.fluid

echo "Step 2b"
stack run -- -r ./step2a.fluid -n rel-ctor-params -a 'data=Expr, ctor=Var, inds=[2,1], reln=`Elem`' > step2b.fluid
stack run -- -c ./step2b.fluid

echo "Step 3a"
stack run -- -r ./step2b.fluid -n add-param -a 'func=lookupVar, index=0, type=`List V`, name=patV' > step3a.fluid
stack run -- -c ./step3a.fluid

echo "Step 3b"
stack run -- -r ./step3a.fluid -n rel-func-params -a 'func=lookupVar, inds=[2,3], reln=`Elem`' > step3b.fluid
stack run -- -c ./step3b.fluid

# Broken: pattern expansion
# Does not typecheck because of impossible cases (intended)
# stack run -- -c ./step3c.fluid
echo "Step 3d"
stack run -- -r ./step3c.fluid -n identify-impossibles -a 'decl=lookupVar' > step3d.fluid
stack run -- -c ./step3d.fluid

# Manual: fill holes + remove case expression
echo "Step 4"
stack run -- -c ./step4.fluid

echo "Step 5a"
stack run -- -r ./step4.fluid -n add-param -a 'func=eval, index=0, type=`List Nat`, name=patV1' > step5a.fluid
stack run -- -c ./step5a.fluid

echo "Step 5b"
stack run -- -r ./step5a.fluid -n rel-func-params -a 'func=eval, inds=[3,2,4], reln=`Unzip`' > step5b.fluid
stack run -- -c ./step5b.fluid

# Broken: pattern expansion
# Does not typecheck because of impossible cases (intended)
# stack run -- -c ./step5c.fluid

echo "Step 5d"
stack run -- -r ./step5c.fluid -n identify-impossibles -a 'decl=eval' > step5d.fluid
stack run -- -c ./step5d.fluid

# Manual: fill holes
echo "Step 6"
stack run -- -c ./step6.fluid

echo "Step 7a"
stack run -- -r ./step6.fluid -n add-param -a 'func=lookupVar, index=0, type=`List Nat`, name=patV2' > step7a.fluid
stack run -- -c ./step7a.fluid

# Broken: pattern expansion does not work
echo "Step 7b"
stack run -- -c ./step7b.fluid

# Manual: fill holes
echo "Step 7c"
stack run -- -c ./step7c.fluid

echo "Step 7d"
stack run -- -r ./step7c.fluid -n rel-func-params -a 'func=lookupVar, inds=[1,4,5], reln=`Unzip`' > step7d.fluid
stack run -- -c ./step7d.fluid

# Broken: pattern expansion
# Not meant to typecheck because of impossible cases
echo "Step 7e"
# stack run -- -c ./step7e.fluid

echo "Step 7f"
stack run -- -r ./step7e.fluid -n identify-impossibles -a 'decl=lookupVar' > step7f.fluid
stack run -- -c ./step7f.fluid

# Manual: fill holes
echo "Step 8"
stack run -- -c ./step8.fluid

# Broken: remove maybe
echo "Step 9"
stack run -- -r ./step8.fluid -n remove-maybe -a 'func=lookupVar' > step9.fluid
stack run -- -c ./step9.fluid

# Step 10 not needed anymore

# Broken: remove maybe
echo "Step 11"
stack run -- -r ./step9.fluid -n remove-maybe -a 'func=eval' > step11.fluid
stack run -- -c ./step11.fluid
