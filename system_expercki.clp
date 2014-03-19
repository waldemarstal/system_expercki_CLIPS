;;;=====================================================
;;;   Expercki system wyboru przedmiotów
;;;
;;;     Prosty system expercki, pomagający w wyborze
;;;     przedmiotów na dany semestr na WMI.
;;;     Przedmioty wybierane są z puli przedmiotów  
;;;     obowiązkowych i gwarantowanych.

;;;     Bazą wiedzy jest zbiór faktów o przedmiotach:
;;;       - nazwa, 
;;;		  - rodzaj (inf, mat),
;;;       - semestr (przedmioty odbywają się w semestrze
;;;		    letnim, zimowym lub obu),
;;;		  - wyagania (brak lub zaliczenie danych
;;;		    przedmiotów),
;;;		  - wyznacznik - określający wartość(priorytet) przedmiotu, która
;;;			zwiększona będzie gdy przedmiot będzie miał dane 
;;;			atuty a zmniejszana w przeciwnym wypadku
;;;		oraz dane studenta o jego:
;;;		  - preferencjach (inf, mat),
;;; 	  - interesującym go semestrze 
;;;			(letni, zimowy lub oba),
;;; 	  - przedmiotach już zaliczonych,
;;; 
;;;		
;;;		Oznaczenia przedmiotów:
;;;		  - AM   - Analiza matematyczna
;;;		  - L    - Logika
;;;		  - A    - Algebra
;;;		  - P    - Programowanie
;;;		  - MD   - Matematyka Dyskretna
;;;		  - RP   - Rachunek Proawdopodobieństwa
;;;		  - AN   - Analiza numeryczna
;;;		  - AiSD - Algorytmy i struktury danych
;;;		  - WDI  - Wstęp do informatyki
;;;		  - ASK  - Architektura systemów 
;;;				   komputerowych
;;;		  - SO   - Systemy operacyjne
;;;		  - SK   - Sieci komputerowe
;;;		  - IO   - Inżynieria oprogramowania
;;;		  - KCK  - Komunikacja człowiek - komputer
;;;		  - SW   - Systemy wbudowane
;;;		  - BD   - Bazy danych
;;;		  - SI   - Sztuczna inteligencja
;;;		  - PGK  - Podstawy grafiki komputerowej
;;;			
;;;		
;;;     CLIPS Version 6.3
;;; 
;;;     Uruchomienie: load buffer, reset and run.
;;;     Odpwoiedzi na pytania: tak lub nie.
;;;=====================================================


;;;***************************
;;;* DEFTEMPLATE DEFINITIONS *
;;;***************************

(deftemplate przedmiot
	(slot nazwa (type SYMBOL) (default ?NONE))
	(slot rodzaj (type SYMBOL) 
		(allowed-symbols inf mat) 
		(default ?DERIVE))
	(slot semestr (type SYMBOL) 
		(allowed-symbols oba zimowy letni)
		(default ?DERIVE))
	(multislot wymagania
		(type SYMBOL))
	(slot wyznacznik (type INTEGER) (default ?NONE))
)

(deftemplate student
	(multislot preferencje (type SYMBOL) 
		(allowed-symbols inf mat) 
		(default ?DERIVE))
	(slot semestr (type SYMBOL) 
		(allowed-symbols oba zimowy letni)
		(default ?DERIVE))
	(multislot zaliczone
		(type SYMBOL))
)

;;;***************************
;;;* DEFFACTS KNOWLEDGE BASE *
;;;***************************

(deffacts przedmioty
	(przedmiot (nazwa AM) (rodzaj mat)  
		(semestr zimowy) (wyznacznik 1))
	(przedmiot (nazwa L) (rodzaj mat)  
		(semestr zimowy) (wyznacznik 1))
	(przedmiot (nazwa A) (rodzaj mat)  
		(semestr letni) (wyznacznik 1))
	(przedmiot (nazwa P) (rodzaj inf)  
		(semestr letni) (wyznacznik 1))
	(przedmiot (nazwa MD) (rodzaj mat)  
		(semestr zimowy) (wyznacznik 1))
	(przedmiot (nazwa RP) (rodzaj mat)  
		(semestr letni) (wymagania AM)
		(wyznacznik 1))
	(przedmiot (nazwa AN) (rodzaj mat)  
		(semestr zimowy) (wymagania AM A)
		(wyznacznik 1))
	(przedmiot (nazwa AiSD) (rodzaj inf)  
		(semestr letni) (wymagania MD)
		(wyznacznik 1))
	(przedmiot (nazwa ASK) (rodzaj inf)  
		(semestr zimowy) (wyznacznik 1))
	(przedmiot (nazwa SO) (rodzaj inf)  
		(semestr zimowy) (wyznacznik 1))
	(przedmiot (nazwa SK) (rodzaj inf)  
		(semestr letni) (wymagania A)
	    (wyznacznik 1))
	(przedmiot (nazwa IO) (rodzaj inf)  
		(semestr zimowy) (wymagania BD P)
	    (wyznacznik 1))
	(przedmiot (nazwa KCK) (rodzaj inf)  
		(semestr zimowy) (wyznacznik 1))
	(przedmiot (nazwa SW) (rodzaj inf)  
		(semestr zimowy) (wyznacznik 1))
	(przedmiot (nazwa BD) (rodzaj inf)  
		(semestr letni) (wymagania L AiSD)
	    (wyznacznik 1))
	(przedmiot (nazwa SI) (rodzaj inf)  
		(semestr letni) (wymagania AiSD MD L)
	    (wyznacznik 1))
	(przedmiot (nazwa PGK) (rodzaj inf)  
		(semestr zimowy) (wymagania A AiSD AN)
	    (wyznacznik 1))
)

(deffacts dane_studenta
	(student (preferencje mat inf) (semestr letni zimowy)
		(zaliczone AM L A P))
	(semestr oba)
	(sprawdz_inf)
	(sprawdz_mat)
)

;;;**************************
;;;* INFERENCE RULES        *
;;;**************************

(defrule usun_przedmioty_z_innego_semestru
	(declare (salience 10))
	(student (semestr ?x))
	(not(semestr ?x))
	?fact <- (przedmiot (semestr ~?x))
	=>
	(printout t "retracting " ?fact crlf)
  	(retract ?fact)
)

(defrule podpowiedz_przedmioty_inf
	(sprawdz_inf)
	(student (preferencje ?x $?))
	(przedmiot (nazwa ?n)(rodzaj ?x) (wyznacznik ?wx))
	=>
	(assert (zwieksz_inf ?n))
)

(defrule podpowiadanym_przedmiotom_zwieksz_wyznacznik_inf
	?f <- (sprawdz_inf)
	(forall 
		(and
			(student (preferencje ?x $?))
			(przedmiot (nazwa ?n)(rodzaj ?x) (wyznacznik ?wx))
		)
		(zwieksz_inf ?n)
	)
	=>
	(retract ?f)
	(assert (uaktualnij_wyznacznik_inf))
)

(defrule uaktualnij_wyznacznik_inf
	?f <- (przedmiot (nazwa ?n) (rodzaj ?x) (wyznacznik ?wx))
	?f2 <- (zwieksz_inf ?n)
	(uaktualnij_wyznacznik_inf)
	=>
	(modify ?f (wyznacznik (+ 2 ?wx)))
	(retract ?f2)
)

(defrule ukatualniono_wyznacznik_inf
	?f1 <- (uaktualnij_wyznacznik_inf)
	(not (zwieksz_inf ?))
	=>
	(retract ?f1)
)

(defrule podpowiedz_przedmioty_mat
	(sprawdz_mat)
	(student (preferencje ? ?x))
	(przedmiot (nazwa ?n)(rodzaj ?x) (wyznacznik ?wx))
	=>
	(assert (zwieksz_mat ?n))
)

(defrule podpowiadanym_przedmiotom_zwieksz_wyznacznik_mat
	?f <- (sprawdz_mat)
	(forall 
		(and
			(student (preferencje ? ?x))
			(przedmiot (nazwa ?n)(rodzaj ?x) (wyznacznik ?wx))
		)
		(zwieksz_mat ?n)
	)
	=>
	(retract ?f)
	(assert (uaktualnij_wyznacznik_mat))
)

(defrule uaktualnij_wyznacznik_mat
	?f <- (przedmiot (nazwa ?n) (rodzaj ?x) (wyznacznik ?wx))
	?f2 <- (zwieksz_mat ?n)
	(uaktualnij_wyznacznik_mat)
	=>
	(modify ?f (wyznacznik (+ 2 ?wx)))
	(retract ?f2)
)

(defrule ukatualniono_wyznacznik_mat
	?f1 <- (uaktualnij_wyznacznik_mat)
	(not (zwieksz_mat ?))
	=>
	(retract ?f1)
)

(defrule wnioski_z_zaliczen
	(student (zaliczone $?x))
	=>
	(loop-for-count (?i 1 (length $?x)) do 
		(assert(zaproponuj_kontunuacje (nth$ ?i $?x)))
		(assert(zaliczone_do_wymagan (nth$ ?i $?x)))
	)
)

(defrule dodaj_wymagania
	(przedmiot (nazwa ?n) (wymagania $?x))
	=>
	(loop-for-count (?i 1 (length $?x)) do 
		(assert(wymaga ?n (nth$ ?i $?x)))
		(assert(wymaga2 ?n (nth$ ?i $?x)))
	)
)

(defrule odradzaj_wymagan
	(not (zaliczone_do_wymagan ?x))
	?f2 <- (wymaga ?y ?x)
	?f3 <- (przedmiot (nazwa ?y) (wymagania $?wy)(wyznacznik ?w))
	=>
	(modify ?f3 (wyznacznik (- 2 ?w)) (wymagania ))
	(retract ?f2)
)

(defrule proponuj_wymagania
	?f1 <- (zaliczone_do_wymagan ?x)
	?f2 <- (wymaga2 ?y ?x)
	?f3 <- (przedmiot (nazwa ?y) (wymagania $?wy)(wyznacznik ?w))
	=>
	(modify ?f3 (wyznacznik (+ 2 ?w)) (wymagania ))
	(retract ?f1)
	(retract ?f2)
)

(defrule proponowane_kontynucje_i_usun_zaliczone
	?f1 <- (zaproponuj_kontunuacje ?x)
	?f2 <- (przedmiot (nazwa ?x))
	=>
	(if (eq ?x AM) then 
		(assert(zwieksz_priorytet AN)) 
		(assert(zwieksz_priorytet A))
		(assert(zwieksz_priorytet RP))
	)
	(if (eq ?x L) then 
		(assert(zwieksz_priorytet MD))
		(assert(zwieksz_priorytet A))
		(assert(zwieksz_priorytet BD))
		(assert(zwieksz_priorytet SI))
	)
	(if (eq ?x A) then 
		(assert(zwieksz_priorytet SK))
		(assert(zwieksz_priorytet PGK))
	)
	(if (eq ?x P) then 
		(assert(zwieksz_priorytet IO))
		(assert(zwieksz_priorytet SO))
		(assert(zwieksz_priorytet SI))
		(assert(zwieksz_priorytet SW))
	)
	(if (eq ?x MD) then 
		(assert(zwieksz_priorytet AiSD))
		(assert(zwieksz_priorytet SI))
		(assert(zwieksz_priorytet PGK))
	)
	(if (eq ?x ASK) then (assert(zwieksz_priorytet SW)))
	(if (eq ?x AiSD) then (assert(zwieksz_priorytet BD)))
	(retract ?f1)
	(retract ?f1)
)

(defrule usun_zbedne_proponowane
	?f1 <- (zaproponuj_kontunuacje ?x)
	(not (przedmiot (nazwa ?x)))
	=>
	(retract ?f1)
)

(defrule usun_zbedne_zwiekszane_a_niobecne
	?f1 <- (zwieksz_priorytet ?x)
	(not (przedmiot (nazwa ?x)))
	=>
	(retract ?f1)
)

(defrule zwieksz_priorytet
	?f <- (zwieksz_priorytet ?x)
	?f2 <- (przedmiot (nazwa ?y) (wyznacznik ?w))
	=>
	(modify ?f2 (wyznacznik (+ 2 ?w)) (wymagania ))
	(retract ?f)
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