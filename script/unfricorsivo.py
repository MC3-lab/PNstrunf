#!/usr/bin/python3.4
# coding: utf-8
#
"""Winning strategy for the reachability of a target transition. 

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

Parameters
----------
net: ndr file
    The net must be provided in ndr format. This is a textual format 
    used to describe graphics produced with nd editor in TINA.
    More information at: http://projects.laas.fr/tina/manuals/formats.html.
"""

import numpy as np 
from Cut import *
from sys import argv
import copy
import string
import copy

def help():
    print("Instruction to run the program:")
    print(" |python3 unfricorsivo.py -n [file with the net]")
    print(" |")
    print(" |Mandatory flag and argument:")
    print(" |-n or --net   input_path + file_name ")
    print(" |")
    print(" |Example:")
    print(" |To load the net 'rete.ndr' in the current folder write")
    print(" |python3 unfricorsivo.py -n rete.ndr")
    exit()

def tree_exploration (net, k, target, cut, M, Elist, e, st, beta, tree, ind, scattati, ver, sz):
    """Recursive function which explore a cut in the unfolding.

    This function find the existence of a winning strategy by exploring 
    all the prefixes of palys in the unfolding. 
    For every play, it explores first uncontrollable events, waiting as 
    much as possible before firing every controllable event.  

    Parameters
    ---------
    net: list
        Incidence matrix of the net
    k: int
        Column number of the first controllable transition
    target: int
        Column number of the target transition
    cut: list
        List formed by two lists, the first describing the current 
        marking, the second with the indices of places in the marking
    M: list
        List of markings visited in the current play 
    Elist: 

    e: int
        Last event added in the current play
    st: list
        List of pair 'marking'-'transition to choose' which represent 
        the strategy already computed 
    tree: list
        List of triples cut-event-cut that represent the prefix of the 
        unfolding
    ind: list 
        Index of the last cut that has been considered
    scattati: list
        List of events that are already part of the prefix
    ver: list    
        List of pairs repeated marking- events fired between the 
        two repetitions
    sz: list
        Events that fired in a cycle or that are in conflict with 
        events that fired in a cycle

    Returns 
    -------
    w2: bool
        It states if there is a winning strategy, knowing that the play 
        reached the cut 'cut'.
    st: list
        Winning strategy (if there is one)  
    tree: list
        List of prefixes of the winning plays  
    ver: list    
        List of pairs repeated marking- events fired between the 
        two repetitions
    """
    
    global contatore
    contatore = contatore + 1 # count the number of recursive calls
    enab = calcola_abilitati(net, cut[0]) 
    enab = enab - sz
    if e == target: #the target occurred
        return True, st, beta, tree, ver
    elif 1 not in enab: #deadlock
        return False, st, beta, tree, ver
    elif confronta_tagli(cut, taglic) == True: #the cut was already analysed and after that the user loses
        return False, st, beta, tree, ver
    elif confronta_tagli(cut, taglib): #the cut was already analysed and after that the user wins
        return True, st, beta, tree, ver
    elif set(cut[0]) in M: #the marking was already crossed in the play
        return explore_cut_c(net, k, target, st, beta, tree, enab, cut, M, Elist, ind, scattati, ver, sz)
    else:
        E = []
        for i in range (0, len(enab)):
            if enab[i] == 1:
                E.append(i)
        flag_nc = False
        w2 = False
        choices = set([])
        lose = set([])
        while E != []: 
            e0, E = extract(E)
            precond = calcola_precond(net, e0, cut)
            #In order to compute the indices of places of the cut following 
            #e0, we divide the case in which e0 has already been considered 
            #from the case in which it is a new event.
            if [precond, e0] in scattati:     
                ecut = calcola_taglio_successivo(cut, e0, net, ind, False)
            else:        
                ind[np.shape(net)[0] + e0 ] = ind[np.shape(net)[0] + e0] + 1
                ecut = calcola_taglio_successivo(cut, e0, net, ind)
                scattati.append([precond, e0])
#                  
            Elist1 = copy.deepcopy(Elist)
            Elist1.append(e0) 
            M1 = copy.deepcopy(M)
            M1.append(set(cut[0]))
#    
            if e0 < k:
                flag_nc = True
                w, st, beta, tree, ver = tree_exploration(net, k, target, ecut, M1, Elist1, e0, st, beta, tree, ind, scattati, ver, sz)
                #The prefix is updated every time that the recursive call returns True
                for i in range (0, len(ver)):
                    if set(ecut[0]) == ver[i][0] and (set(cut[0]), ver[i][1]) not in ver:
                        ver.append((set(cut[0]), ver[i][1]))                 
                if w == True:
                    tree.append((cut, [e0, ind[np.shape(net)[0] + e0] -1], ecut)) 
                else:
                    taglic.append(cut)
                    return False, st, beta, tree, ver          
            else:
                w, st, beta, tree, ver = tree_exploration(net, k, target, ecut, M1, Elist1, e0, st, beta, tree, ind, scattati, ver, sz)
                if w == True:
                    tree.append((cut, [e0, ind[np.shape(net)[0] + e0] -1], ecut))
                    choices.add(e0)  
                    w2 = True
                else:
                    lose.add(e0)
        if w2 == True:
            st.append([cut, choices])  #since e0 is controllable, if the recursive call returns True, the strategy is updated
        elif w2 == False and flag_nc == False: 
            taglic.append(cut)
            return False, st, beta, tree, ver
        if lose != set([]):
            beta.append([cut, lose])
        taglib.append(cut)  
        ins = set([])
        j = 0
        for i in range (0, len(ver)):
            if set(cut[0]) == ver[i][0]:
                j = j+1
                ins = ins.union(set(ver[i][1]))
        if j >= 1:
            sz1 = stable_zone(net, ins)
            w, st, beta, tree, ver = tree_exploration(net, k, target, cut, M, Elist, -1, st, beta, tree, ind, scattati, ver, sz1)
        else:
            return True, st, beta, tree, ver

        return w, st, beta, tree, ver


def explore_cut_c(net, k, target, st, beta, tree, enab_c, cut, M, Elist, ind, scattati, ver, sz): 
    """Function used in case of repeated marking in a play. 

    When the same marking appears twice or more in a play, this 
    function check if there are enabled transitions that are concurrent 
    with all the transitions occurred between the first and the last 
    occurrence of the repeated marking. If there are, they are added to 
    the prefix, and the function 'tree_exploration' is called again. 
     

    Parameters
    ----------
    net: list
        Incidence matrix of the net
    k: int
        Column number of the first controllable transition
    target: int
        Column number of the target
    st: list
        List cut-transition describing the strategy already computed
    tree: list
        List cut-transition-cut describing the prefix already computed
    enab_c: np.array
        Array filled with 0 in the positions in which the associated 
        transition is not enabled in the cut 'cut', 1 in the postitions 
        of the enabled transitions.
    cut: list
        Cut that has to be analysed 
    M: list
        List of markings already visited in the current play 
    Elist: list
        List of events that occurred in the play
    ind: list
        Identifier of the cut in the play 
    scattati: list
        List of events already occurred in the unfolding
    ver: list    
        List of pairs repeated marking- events fired between the 
        two repetitions
    sz: list
        events that fired in a cycle or are in conflict with them

    Returns
    -------
    w2: bool
        It states the existence of a strategy from the input cut 
    st: list
        winning strategy, if there is one
    tree: list
        prefix of the unfolding represented as list of triples 
        cut-transition-cut  
    ver: list    
        List of pairs repeated marking- events fired between the 
        two repetitions      
    """

    E, index = f(net, enab_c, set(cut[0]), M, Elist, k)
    global contatore
    contatore = contatore+1
    if E == set([]):
        return False, st, beta, tree, ver
#
    for i in range (0, len(sz)):
        if sz[i] == 1:
            E = E - set([i])
    E = list(E)
    flag_nc = False
    w2 = False
    choices = set([])
    lose = set([])
#
    while E != []: 
        e0, E = extract(E)
        precond = calcola_precond(net, e0, cut)
        #In order to compute the indices of places of the cut following 
        #e0, we divide the case in which e0 has already been considered 
        #from the case in which it is a new event.
        if [precond, e0] in scattati:     
            ecut = calcola_taglio_successivo(cut, e0, net, ind, False)
        else:        
            ind[np.shape(net)[0] + e0 ] = ind[np.shape(net)[0] + e0] + 1
            ecut = calcola_taglio_successivo(cut, e0, net, ind)
            scattati.append([precond, e0])
#                   
        Elist1 = copy.deepcopy(Elist)
        Elist1.append(e0)
        M1 = copy.deepcopy(M)
        M1.append(set(cut[0]))
#    
        if e0 < k:
            flag_nc = True
            w, st, beta, tree, ver = tree_exploration(net, k, target, ecut, M1, Elist1, e0, st, beta, tree, ind, scattati, ver, sz)
            #The prefix is updated every time that the recursive call returns True
            if w == True:
                tree.append((cut, [e0, ind[np.shape(net)[0] + e0] -1], ecut)) 
            else:
                taglic.append(cut)
                return False, st, beta, tree, ver          
        else:
            w, st, beta, tree, ver = tree_exploration(net, k, target, ecut, M1, Elist1, e0, st, beta, tree, ind, scattati, ver, sz)
            if w == True:
                tree.append((cut, [e0, ind[np.shape(net)[0] + e0] -1], ecut))
                choices.add(e0)  
                w2 = True
            else:
                lose.add(e0)
    if w2 == True:
        st.append([cut, choices])  #since e0 is controllable, if the recursive call returns True, the strategy is updated
    elif w2 == False and flag_nc == False: 
        taglic.append(cut)
        return False, st, beta, tree, ver
    if lose != set([]):
        beta.append([cut, lose])
    taglib.append(cut) 
    ver.append((set(cut[0]), Elist[index:len(Elist)]))  
    return True, st, beta, tree, ver


def f(net, enab_c, cut, M, Elist, k):
    """Check if there are transitions concurrent with cycles.

    This function verifies which events are enabled in all the markings 
    after the first occurrence of the marking associated to 'cut'.
    
    Parameters
    ---------
    net: list
        Incidence matrix of the net
    enab_c: list
        List of enabled transitions in 'cut'
    cut: set
        Marking of the cut that we are currently considering and whose 
        associated marking is repeated
    M: list
        List of markings already visited in the play 
    Elist: list
        List of events that occurred in the play
    k: int
        index of the first controllable transition

    Rerutns
    --------
    E: list
        List of enabled transitions that are concurrent with the cycle 
    i: int 
        index in M and Elist of the first repeated marking    
    """

    i = 0
    while M[i] != cut : #look for the first occurrence of 'cut'
        i = i +1
    E = set([])
    for l in range (0, len(enab_c)): #check if l was enabled in all the marking of the cycle
        if enab_c[l] == 1:
            j = i
            if Elist[j] >= k:
                return set([]), i
            while j < len(M) and verifica_ab(net, M[j], l):              
                j = j +1
            if j == len(M):
                E.add(l)
    return E, i

def g(net, marking, E, k):
    nprecond = set([])
    ev = set([])
    for i in E:
        for j in range (0, np.shape(net)[0]):
            if net[j][i] == -1: 
                nprecond.add(j)
    for i in nprecond:
        for j in range(0, k):
            if net[i][j] == -1 and verifica_ab(net, marking, j):
                ev.add(j)
    return(ev)
    
def stable_zone(net, ins):
    """Select the events that occurred in a cycle and those that are 
       in conflict with them

    Parameters
    ----------
    net: np.array
        incidence matrix of the net
    ins: set
        set of events
    
    Returns
    -------
    sz: list
        events in conflict with those in 'ins' (end ins itself)

    """
    rows = set([])
    sz = np.zeros(np.shape(net)[1])
    for i in ins:
        for j in range (0, np.shape(net)[0]):
            if net[j][i] == -1:
                rows.add(j)
    for l in rows:
        for j in range (0, np.shape(net)[1]):
            if net[l][j] == -1:
                sz[j] = 1
    return sz
                           
def calcola_abilitati(rete, marcatura):
    """Compute enabled transitions.

    Given the net 'rete' and the marking 'marcatura', the enabled 
    transitions in 'marcatura' are those that have all their 
    precondition in 'marcatura'.

    Parameters
    ----------
    rete: list
        Incidence matrix of the net
    marcatura: set
        Current marking 

    Returns
    -------
    np.array
       array in which is specified wether every transition is enabled 
       in 'marcatura' 
    """

    abilitati = np.zeros(np.shape(rete)[1], int)    
    for i in range (0, np.shape(rete)[1]):
        if verifica_ab(rete, marcatura, i):
            abilitati[i] = 1
    return abilitati

def verifica_ab(net, m, e):
    """Given a transition, check if it is enabled in a certain marking.

    Parameters
    ----------
    net: list
        Incidence matrix
    m: list/set
        Marking
    e: int
        Transition 

    Returns
    -------
    bool
        True if 'e' is enabled in 'm', False otherwise 

    """
    for j in range (0, np.shape(net)[0]):
        if net[j][e] == -1:
            if j not in m:
                return False
    return True

def calcola_taglio_successivo(taglio_prec, evento, rete, ind, nuovo = True):
    """Compute the cut following the occurrence if a given transition.
    
    Parameters
    ----------
    taglio_prec: list
        Cut from which the transition 'evento' occurs 
    evento: int
        Event that is added to the prefix
    rete: list
        Incidence matrix of the net
    ind: list
        Index of the last cut that has been considered
    nuovo: bool, optional
        It indicate if the event is considered for the first time or it 
        was already added to the unfolding

    Returns
    -------
    disp: list
        Cut in the unfolding that follows the occurrence of 'evento'
    """

    taglio = copy.deepcopy(taglio_prec[0])
    post = []
    #From the current cut, the precondition are removed and postcondition are added
    for i in range (0, np.shape(rete)[0]):
        if rete[i][evento]==-1:
            taglio.remove(i)
        if rete[i][evento] == 1:
            taglio.append(i)
            post.append(i)
    valori = []
    for i in taglio :
        #If it is the first time that the event is considered, 
        #the indices of postconditions are updated
        if i in post and nuovo == True:
            ind[i] = ind[i] + 1          
        valori.append(ind[i] -1)            
    disp = [taglio]
    disp.append(valori)
   
    return disp

def confronta_tagli (taglio, lista_tagli):
    """Check if a cut is already in a list.

    Parameters
    ----------
    taglio: list
      Cut to look for in the list
    lista_tagli: list
      list in which we look for the cut
    
    Returns
    -------
    bool
      True if the cut is in the list, False otherwise

    """
    for t in lista_tagli:
        b = confronto(t[0], t[1], taglio[0], taglio[1])        
        if b == True:
            return True
    return False

def confronto (x, y, v, w):
    """Comparison of two cuts: [x, y] and [v, w]. 
      
    Parameters
    ----------
    x: list
      places in the first cut
    y: list 
      indices of the places in the first cut
    v: list
      places in the second cut
    w: list
      indices of the places in the second cut

    Returns 
    -------
    bool
      True if the cuts are equals, False otherwise  

    """
    for i in range(0,len(x)):
        if x[i] in v:
            if y[i] != w[v.index(x[i])]:
                return False
        else:
            return False
    return True 

def calcola_precond (net, ev, cut) :
    """Computation of the precondition of a given event.

    Parameters
    ----------
    net: list
        Incidence matrix of the net
    ev: int
        Event of which we want to compute the preconditions
    cut: list
        Cut in which there are the preconditions of 'ev'

    Returns
    -------
    precond: list
        List of event's preconditions denoted as list of pair 
        place-indices
    """

    precond = []
    for i in range (0, np.shape(net)[0]) :
        if net[i][ev] == -1 :
            p = cut[1][cut[0].index(i)]
            precond.append([i, p])
    return precond

def extract(E):
    """Extraction of the first element of a list.

    Parameters
    ----------
    E: list
        List of enabled events
        
    Returns
    -------
    e0: int 
        First element of the list 'E'
    E: list
        Input list modified without the first element
    """

    e0 = E[0]
    E.pop(0)
    return e0, E


def Elimina(lista):
    """Deleting repeated elements from a list.

    Parameters
    ----------
    lista: list
        List that could have repeated elements inside

    Returns
    -------
    lista: list
        List in which all the elements are different
    """

    copia = copy.deepcopy(lista)
    for i in copia :
        if lista.count(i) > 1:
            lista.remove(i)
    return lista

def visualizza_strategia (elenco, m) :
    """From the incidence matrix to the name in the .ndr file. 

    This function takes the strategy in which places and transitions 
    are described with the numers of rows and columns in the incidence 
    matrix and returns the strategy in which places and transtions have 
    the same name as in the .ndr file.

    Parameters
    ----------
    st: list 
        Strategy in which places and transitions are numbers 
    m: list
        Incidence matrix in which the name of places and transition is 
        specified

    Returns
    -------
    strategy: list
        Strategy in which the name of places and transitions are as in 
        the .ndr file
    """

    strategy = []    
    for k in range(0, len(elenco)) :
        i = elenco[k][0]
        i = list(i)
        l = elenco[k][1]
        l = list(l)
#        print("m", m)
        c = []
        d = []
        for j in range(0,len(i)):         
            c.append(m[i[j] + 1][0])
        for h in range(0, len(l)):
            d.append(m[0][l[h]+1])
        strategy.append([c, d])
    return strategy


def input_parameters(rete):
    """Extraction of the useful data from the file .ndr.

    This function asks the user which are the controllable transitions 
    and the target, and computes the incidence matrix of the net.

    Parameters
    ----------
    rete: str
        In the string there is the path of the file with the 
        description of the net
  
    Returns
    -------
    matrice_aux: list
        Matrix describing the relations between places and transitions 
        in the net, and their relation with the incidence matrix
    m: list
        Incidence matrix
    control: int 
        Index of the first column with a controllable transition
    t: int
        Index of the target transition
    s: set
        Initial marking 

    """

    f = open (rete, "r")
    num_righe = 0
    num_colonne = 0
    while 1:
	    cont = 0
	    c = f.readline()
	    if c[0] == 'e':
		    break
	    if c[0] == 'p':
		    num_righe = num_righe + 1
	    if c[0] == 't':
		    num_colonne = num_colonne + 1
    m = [[] for i in range(num_righe+1)]
    for row in m:
	    for i in range(num_colonne+1):
		    row.append(" ")
    f.close()
    f = open (rete, "r")
    m[0][0] = 'N'
    num_righe = 0
    num_colonne = 0
    mark = []
    marc = []
    while 1:
	    cont = 0
	    c = f.readline()
	    if c[0] == 'e':
		    break
	    else:
		    if c[0] == 'p':
			    num_righe = num_righe + 1
			    m[num_righe][0] = c.split()[3]
			    if c.split()[4] != '0':
				    marc.append(c.split()[3])
				    mark.append(c.split()[3] + '=' +c.split()[4])
		    else:
			    if c[0] == 't':
				    num_colonne = num_colonne + 1
				    m[0][num_colonne] = c.split()[3]
    while 1:
	    t = False
	    riga = 0
	    colonna = 0
	    cont = 0
	    nome = c.split()[1]
	    nome1 = c.split()[2]
	    for row in m:
		    if nome in row:
			    if cont == 0:
				    colonna = row.index(nome)
			    else:
				    riga = cont
				    t = True
			    break
		    cont = cont + 1
	    cont = 0
	    for row in m:
		    if nome1 in row:
			    if cont == 0:
				    colonna = row.index(nome1)
			    else:
				    riga = cont
			    break
		    cont = cont + 1
	    if t != True:
		    m[riga][colonna] = c.split()[3]
	    else:
		    m[riga][colonna] = '-' + c.split()[3]
	    c = f.readline()
	    if c[0] != 'e':
		    break

    f.close()

    m = [[x.replace(' ','0') for x in i] for i in m]


    print("INCIDENCE MATRIX WITH TRANSITIONS ORDERED RANDOMLY: ")
    for i in range(0,num_righe+1):
	    print(m[i])

    mark_num = []
    for j in range (0,len(marc)):
	    for i in range(0,num_righe+1):
		    if m[i][0] == marc[j]:
			    mark_num.append(i-1)

    vettore = input("Controllable transitions (separated by a space): ")
    vettore = vettore.split()
    volte = 0
    i = 0
    for i in range(0,len(vettore)):
	    indice = 0
	    volte = volte + 1
	    controllabile = vettore[i]
	    vett = []
	    indice = m[0].index(controllabile)
	    for row in m:
		    vett.append(row[indice])
	    for i in range(0,num_righe+1):
		    m[i].append(vett[i])
	    for row in m:
		    del row[indice]

    control = (len(m[0]) - volte) - 1

    n = input("Target : ")
    t = (m[0].index(n)) - 1

    print("ORDERED INCIDENCE MATRIX")
    for i in range(0,num_righe+1):
	    print(m[i])

    matrice_aux = copy.deepcopy(m)

    del m[0]
    for row in m:
       del row[0]

    for i in range(0,num_righe):
	    m[i] = list(map(int, m[i]))
    print("INCIDENCE MATRIX WITH ONLY NUMBERS")
    print(m)

    print("INITIAL MARKING : ", mark)

    print("INITIAL MARKING EXPRESSED WITH NUMBERS : ",mark_num)

    print("INDEX OF THE FIRST CONTROLLABLE EVENT : ",control)

    print("TARGET : ",t)

    s = mark_num

    return matrice_aux, m, control, t, s 

def parseArguments(parameter):
    """Function that interprets input parameters.

    Parameters
    ----------
    parameter: argv
        Input parameters

    Returns
    -------
    options: dict
        Classification of the input
    """

    if len(parameter) == 1:
        help()

    options = {}
    for i in range(len(parameter)):
        if parameter[i] == '-n' or parameter[i] == '--net':
            options['path_to_net_file'] = parameter[i+1]

    return options

if __name__ == '__main__':
    global contatore 
    contatore = 0
    taglib = [] 
    taglic = []
    opt = parseArguments(argv)
    print(opt)
    m, net, control, target, inMarking = input_parameters(opt['path_to_net_file'])
    ind = np.zeros(np.shape(net)[0] + np.shape(net)[1], int)
    inCut = inMarking
    indici = np.zeros(len(inCut), int)
    indici = list(indici)
    inCut = [inCut]
    inCut.append(indici) #initial cut (marking + indices of the places)

    for i in inMarking : #update of the indices that are in the initial marking
        ind[i] = 1
     
    v, st, beta, tree, ver = tree_exploration(net, control, target, inCut, [], [], -1, [], [], [], ind, [], [], np.zeros(np.shape(net)[1]))
    print(v)
    print("chiamate a tree_exploration: ", contatore)
    #
    if v == True:
        gr_ad = graph_construction(tree)
        print("dimensione grafo: ", len( gr_ad))
        inCut = list_to_Cut(inCut)
        for i in range (0, len(st)):
            st[i][0] = list_to_Cut(st[i][0])  #The cuts in the strategy (list) are transformed in Cut objects.
        for i in range(0, len(beta)):
            beta[i][0] = list_to_Cut(beta[i][0])            
        st1 = []        
        for s in st:
            st1.append([s[0].marking(), s[1]])
        beta1 = []
        for b in beta:
            beta1.append([b[0].marking(), b[1]])
        st1 = Elimina(st1)
        beta1 = Elimina(beta1)
        st_lett = visualizza_strategia(st1, m)
        beta_lett = visualizza_strategia(beta1, m)
        print("alpha: ", st_lett)
        print("beta: ", beta_lett)

