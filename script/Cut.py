class Cut(object):
    """This class describe a cut of the unfolding.
    """
    
    def __init__(self, places = {}):
        self.places = places

    def marking(self):
        """Return the marking associate with the cut.
        """

        return set(self.places.keys())

    def __eq__(self, cut):
        """Establish if two cuts are equals.
        """
        return self.places == cut.places

    def __repr__(self):
        """ Print the cuts.
        """
        s = "  %s" % repr(self.places)
        return s

def graph_construction(albero):
    """Construction of the adjacency matrix.

    From the set of triples describing the prefix, this function 
    construct the adjacency matrix of the prefix.

    Parameters
    ----------
    albero: list
        List of triples describing the prefix
    ad: list
        Adjacency matrix of the prefix of the unfolding 
    """
    ad = [] 
    tagli = [] 

    for tripla in albero :
        c = tripla[2]
        tagliofin = list_to_Cut(c)
        c = tripla[0]
        taglioin = list_to_Cut(c)
        if tagliofin in tagli:
            a = tagli.index(tagliofin)
            ad[a][1].append((taglioin, tripla[1]))
        else:
            tagli.append(tagliofin)
            ad.append((tagliofin, [(taglioin, tripla[1])]))
    stampa_grafo(ad)
    return ad

def stampa_grafo(grafo):
    f = open("grafo", "w")
    for i in grafo:
        print(i[0], "  ", i[1], file = f)


def list_to_Cut(lista):
    """Transformation of a list in a Cut object.

    Parameters
    ----------
    lista: list 
        List describing a cut
    
    Returns
    -------
    taglio: Cut
        Cut object describing a cut
    """
    d = {}
    for i in range (0, len(lista[0])):
        d[lista[0][i]] = lista[1][i]
    taglio = Cut(d)
    return taglio

import copy

def cammini(grafo, taglio, iniz, cammino = [], eventi = [], lsc = [], lse = []):
    """Computation of cuts and events crossed to arrive in a given cut.

    This function compute the lists of cuts and events that are in the 
    past of the cut 'taglio'

    Parameters
    ----------
    grafo: list
        Adjacency matrix of the prefix
    taglio: Cut
        Cut of which the function investigates the past
    iniz: Cut
        Initial cut in the unfolding
    cammino: list, optional
        List of cuts in a path
    eventi: list, optional
        List of events in a path
    lsc: list, optional
        List of paths described with cuts
    lse: list, optional
        List of paths described with events

    Returns
    -------
    lse: list
        List of paths described with events
    lsc: list
        List of paths described with cuts 
    """

    cammino1 = copy.deepcopy(cammino)
    cammino1.append(taglio)

    if taglio == iniz:
        lsc.append(cammino1)
        lse.append(eventi)
        return lse, lsc

    i = 0
    while i < len(grafo) and taglio != grafo[i][0]:
        i = i+1
    if i == len(grafo):
        return lse, lsc

    #copy of the cuts in grafo[i][0] in the list 'pila'
    pila = copy.deepcopy(grafo[i][1])
    while pila != []:           
        eventi1 = copy.deepcopy(eventi)
        prox = pila.pop()
        eventi1.append(prox[1])
        lse, lsc = cammini(grafo, prox[0], iniz, cammino1, eventi1, lsc, lse)
    return lse, lsc
