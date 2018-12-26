(deftemplate puerta
	(slot origen)
	(slot destino)
)

(deftemplate objeto
	(slot nombre)
	(slot sala)
	(slot altura (allowed-symbols nil suelo techo))
	(slot lugar (allowed-symbols nil entrada centro fondo))
)

(deftemplate mono
	(slot sala)
	(slot encima-de)
	(slot sostiene)
	(slot hambre (allowed-symbols si no))
)



(deffacts base-hechos
	(puerta (origen comienzo) (destino sala1))
	(puerta (origen sala1) (destino sala2))
	(puerta (origen sala2) (destino sala3))
	(puerta (origen sala3) (destino sala4))
	(puerta (origen sala4) (destino sala5))

	(mono (sala comienzo) (encima-de suelo) (sostiene nada) (hambre si))
	(objeto (nombre mesa) (sala sala5) (lugar fondo))
	(objeto (nombre banana) (sala sala5) (lugar entrada) (altura techo))
)



(defrule marcar-sala-inicial
	(declare (salience 51))
	(mono (sala ?salaActual))
	(not (exists (salaInicial ?)))
	=>
	(assert (salaInicial ?salaActual))
	(printout t "marcamos la sala " ?salaActual " como la sala inicial" crlf)
)

(defrule inicializar-banana-cogida
	(declare (salience 51))
	(mono (sostiene ~banana) (hambre si))
	(not (exists (bananaCogida ?)))
	=>
	(assert (bananaCogida no))
)

(defrule puerta-simetrica
	(declare (salience 50))
	(puerta (origen ?origen) (destino ?destino))
	(not (puerta (origen ?destino) (destino ?origen)))
	=>
	(assert (puerta (origen ?destino) (destino ?origen)))
)

(defrule ir-salaX-salaY-buscando-bananas
	(logical (bananaCogida no))
	?lm <- (mono (sala ?salaActual) (encima-de suelo) (sostiene ?monoSostiene&~banana) (hambre si))
	(objeto (nombre banana) (sala ~?salaActual))
	(puerta (origen ?salaActual) (destino ?salaDestino))
	(not (visitado ?salaDestino))
	=> 
	(assert (mono (sala ?salaDestino) (encima-de suelo) (sostiene ?monoSostiene) (hambre si)))
   	(retract ?lm)
   	(assert (visitado ?salaActual))
   	(printout t "mover de " ?salaActual " a " ?salaDestino crlf)
)

(defrule ir-salaX-salaY-buscando-sala-inicial
	?lm <- (mono (sala ?salaActual) (encima-de suelo) (sostiene banana) (hambre si))
	(puerta (origen ?salaActual) (destino ?salaDestino))
	(not (visitado ?salaDestino))
	(salaInicial ~?salaActual)
	=> 
	(assert (mono (sala ?salaDestino) (encima-de suelo) (sostiene banana) (hambre si)))
   	(retract ?lm)
   	(assert (visitado ?salaActual))
   	(printout t "mover de " ?salaActual " a " ?salaDestino crlf)
)

(defrule coger-banana-suelo
	?bc <- (bananaCogida no)
	?lm <- (mono (sala ?salaActual) (encima-de suelo) (sostiene nada) (hambre si))
	(objeto (nombre banana) (sala ?salaActual) (altura suelo))
=> 
   	(assert (mono (sala ?salaActual) (encima-de suelo) (sostiene banana) (hambre si)))
   	(retract ?lm)
   	(retract ?bc)
   	(printout t "coge la banana del suelo" crlf)
)

(defrule moverMesa 
	(mono (sala ?salaActual) (encima-de suelo) (sostiene nada) (hambre si))
	?lc <- (objeto (nombre mesa) (sala ?salaActual) (lugar ?lugarMesa))
	(objeto (nombre banana) (sala ?salaActual) (lugar ?lugarBanana&~?lugarMesa) (altura techo))
=> 
   	(assert (objeto (nombre mesa) (sala ?salaActual) (lugar ?lugarBanana)))
   	(retract ?lc)
   	(printout t "mueve mesa a " ?lugarBanana crlf)
)

(defrule subir-mesa
	?lm <- (mono (sala ?salaActual) (encima-de suelo) (sostiene nada) (hambre si))
	(objeto (nombre mesa) (sala ?salaActual) (lugar ?lugarMesa))
	(objeto (nombre banana) (sala ?salaActual) (lugar ?lugarMesa) (altura techo))
=> 
   	(assert (mono (sala ?salaActual) (encima-de mesa) (sostiene nada) (hambre si)))
   	(retract ?lm)
   	(printout t "sube a la mesa" crlf)
)

(defrule coger-banana-techo
	?bc <- (bananaCogida no)
	?lm <- (mono (sala ?salaActual) (encima-de mesa) (sostiene nada) (hambre si))
	(objeto (nombre banana) (sala ?salaActual) (altura techo)) 
	=> 
   	(assert (mono (sala ?salaActual) (encima-de mesa) (sostiene banana) (hambre si)))
   	(retract ?lm)
   	(retract ?bc)
   	(printout t "coge la banana del techo" crlf)
)

(defrule bajar-de-mesa-despues-de-coger-banana-del-techo
	?lm <- (mono (sala ?salaActual) (encima-de mesa) (sostiene banana) (hambre si))
=> 
   	(assert (mono (sala ?salaActual) (encima-de suelo) (sostiene banana) (hambre si)))
   	(retract ?lm)
   	(printout t "baja de la mesa" crlf)
)

(defrule comer-banana
	?lm <- (mono (sala ?salaActual) (encima-de suelo) (sostiene banana) (hambre si))
	(salaInicial ?salaActual)
=> 
	(assert (mono (sala ?salaActual) (encima-de suelo) (sostiene nada) (hambre no)))
   	(retract ?lm)
   	(printout t "come la banana" crlf)
)