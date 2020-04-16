# PNstrunf
This tool runs with Python3. The main function is in unfricorsivo.py. 

-----------------------------------------------------------------------
Instruction to run the program:
-------------------------------
Type python3 unfricorsivo.py -n [file with the net]'

Mandatory flag and argument: '-n' or '--net'   input_path + file_name 

Example:
--------
To load the net 'rete.ndr' in the current folder write:
'python3 unfricorsivo.py -n rete.ndr'

-----------------------------------------------------------------------
Aim of the program:
-------------------
Given an elementary distributed Petri net with a set of controllable 
transitions, and for which a target transition is specified, the 
program verifies if a user is always able to fire once the target 
transition in the net, by controlling just the set of controllable 
transitions. In case of positive answer, the program provides a 
winning strategy for the user. 
We assume that the user observes all the occurrences of the transitions 
and controls a sequential component of the Petri net system.

Since the program represents the net as an incidence matrix,  in the 
current version side conditions are not allowed.
We are working for improving the program with more efficient data 
structures.

Parameters
----------
net: ndr file
    The net must be provided in ndr format. This is a textual format 
    used to describe graphics produced with nd editor in TINA.
    More information at: http://projects.laas.fr/tina/manuals/formats.html.

