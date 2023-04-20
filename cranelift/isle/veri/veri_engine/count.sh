cargo test test_named -- --nocapture &> test_named_log.txt
echo "Rules"
cat test_named_log.txt | grep 'VERIFYING rule with name' | sort | uniq &> rule_with_name.txt
cat rule_with_name.txt | wc -l

echo "Type invocations"
cat test_named_log.txt | grep 'Expected result' | wc -l

echo "Inapplicable"
cat test_named_log.txt | grep 'Rule not applicable' | wc -l

echo "Succeeded"
cat test_named_log.txt | grep 'Verification succeeded' | wc -l

echo "Failed"
cat test_named_log.txt | grep 'Expected result: Failure(Counterexample)' | wc -l