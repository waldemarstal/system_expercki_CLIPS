
(assert (ma zwierzak wlosy))

(defrule byc (ma ?x wlosy) =>
           (assert (jest ?x ssakiem))
           (printout t "it’s a " ?x crlf))
(defrule test (not (ma ? futro)) =>
        (printout t "co ma?")
        (assert (ma wielgus (read))))

(deftemplate personal-data
	(slot name)
	(slot age)
	(slot weight)
	(slot smoker)
	(multislot date_of_birth)
)

(deffacts people
	(personal-data (name adam) (weight 60) (age 30) 
		(smoker no) (date-of-birth 18 06 1970))
	(personal-data (name brenda) (weight 120) (age 45) 
		(smoker yes) (date-of-birth 18 06 1955))
	(personal-data (name charles) (weight 120) (age 60)
		(smoker yes)(date-of-birth 18 06 1940))
)

(deffacts data
	(date 18 06 2000)
)



dodaj regułę niech zwiększa priorytet względem prowadzących

(defrule podpowiedz_przedmioty
	(student (preferencje ?x ?))
	(przedmiot (nazwa ?n)(rodzaj ?x) (wyznacznik ?wx))
	=>
	(assert (zwieksz ?n))
)

(defrule podpowiadanym_przedmiotom_zwieksz_wyznacznik
	(student (preferencje ?x ?))
	?f1 <- (przedmiot (nazwa ?n) (rodzaj ?x) (wyznacznik ?wx))
	?f2 <- (zwieksz ?n)
	=>
	(modify ?f1 (wyznacznik (* ?wx 2)))
	(retract ?f2)
)


(defrule obecny_wynik
	(declare (salience -10))
	(przedmiot (nazwa ?n) (wyznacznik ?w))
	=>

	(if (= ?w 1) then 
		(printout t "Na temat przedmiotu " ?n " nie mam zdania" crlf)
	)
	(if (and (> ?w 1) (< ?w 4)) then 
		(printout t "Przedmiot " ?n " warto wziac" crlf)
	)
	(if (and (> ?w 3) (< ?w 7)) then 
		(printout t "Przedmiot " ?n " powinienes wziac" crlf)
	)
	(if (> ?w 6) then 
		(printout t "Przedmiot " ?n " zdecydowanie wez" crlf)
	)
	(if (and (< ?w 1) (> ?w -2)) then 
		(printout t "Przedmiot " ?n " raczej nie bierz" crlf)
	)
	(if (< ?w -3) then 
		(printout t "Przedmiotu " ?n " zdecydowanie nie bierz" crlf)
	)
)