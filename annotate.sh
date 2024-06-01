#!/bin/bash

cd support
python add_knowledge.py

cd ..
cd data
cd data_for_LLM_v2
python t.py