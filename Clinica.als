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


fact TodoServicoTemApenasUmMedico{
	all ser: Servico | one ser.medico
} 


fact TodoMedicoTrabalhaEmAlgumServico {
	//todo medico faz parte do grupo de medicos de algum serviço da clinica
	all med: Medico | some med.~medico
}

fact CadaMedicoEstaParaUmServico {
	//Todo medico faz parte de um serviço e se um medico está em um serviço ele não pode estar em outro simultaneo
	all med: Medico , ser: Servico | (med in ser.medico => (all ser2: Servico  - ser | med !in ser2.medico))

} 


fact LocalizacaoClinicas {} // A definir


pred show[]{}
run show for 30
