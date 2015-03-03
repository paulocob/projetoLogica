module clinica

----assinaturas---

one abstract sig Clinica { 
 localizacao: some Filial
//clinicas: set Clinica 
}

abstract sig Filial {
	servicos: set Servico
}

abstract sig Servico {
	medico: some Medico
}

sig Odontologia, Psicologia, Fisioterapia extends Servico {}

sig Medico{}

one sig CampinaGrande, JoaoPessoa, Patos, SantaRita extends Filial {}


---predicados---
// não tá rodando esse predicado
/*pred temServico[cli: Clinica, servico: Servico] {
	servico in cli
}*/


---fatos----

fact NumServicosClinica {
	// Cada clínica oferece três serviços.
//	all fil: Filial | one o: Odontologia | one p: Psicologia | one f: Fisioterapia
	
	//all fil: Filial | #fil.servicos = 3 
}

fact CadaServicoEstaParaUmaClinica{
	// Os servicos de Odontologia, Psicologia e Fisioterapia estao presentes em toda clinica
	#Servico = 12
	all o: Odontologia, fil: Filial | (o in fil.servicos => (all fil2: Filial - fil | o !in fil2.servicos))
	all p: Psicologia, fil: Filial | (p in fil.servicos => (all fil2: Filial - fil | p !in fil2.servicos))
	all f: Fisioterapia, fil: Filial | (f in fil.servicos => (all fil2: Filial - fil | f !in fil2.servicos))
	
}

fact CadaMedicoEstaParaUmServico{
	// Os servicos de Odontologia, Psicologia e Fisioterapia estao presentes em toda clinica
	#Medico = 12

}


fact TiposServicos {
	// Os servicos de Odontologia, Psicologia e Fisioterapia estao presentes em toda clinica
	all fil: Filial | one o: Odontologia | one p: Psicologia | one f: Fisioterapia |
	let ser = fil.servicos | o in ser and p in ser and f in ser
}

fact TodaFilialPertenceAClinica {
	//Toda filial esta ligada a sua matriz
	all fil: Filial | some fil.~localizacao
//	all fli: Filial | #(fli.odo)
}

fact LocalizacaoClinicas {} // A definir


pred show[]{}
run show for 20
