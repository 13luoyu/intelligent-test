# nohup bash run.sh >../log/run_experiment.log &

python generate_rules_and_testcases_for_experiment.py --model llama2
python generate_rules_and_testcases_for_experiment.py --model mengzi
python generate_rules_and_testcases_for_experiment.py --model finbert

python compute_bsc.py
python draw_bsc_self-compare_figure.py