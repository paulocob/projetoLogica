module clinica

----assinaturas---

one abstract sig Clinica { 
 localizacao: some Filial
}

abstract sig Filial {
	servicos: set Servico
}

abstract sig Servico {
	medico: some Medico,
	ajudante: set Ajudante
}

sig Odontologia, Psicologia, Fisioterapia extends Servico {}

sig Medico{
	pacientes: set Paciente
}

one sig CampinaGrande, JoaoPessoa, Patos, SantaRita extends Filial {}

sig Ajudante{}

sig Paciente{}

----------------------------------- FUNCOES --------------------------------

fun ajudantesDeFisioterapia[ser : Servico]: set Ajudante{
	ser.ajudante		
}

fun getPacientes[med: Medico]: set Paciente{
	med.pacientes
}


--- predicado ---

pred TodaFilialPertenceAClinica {
	//Toda filial esta ligada a sua matriz
	all fil: Filial | some fil.~localizacao
}

pred TodaFilialTem3Servicos {
	// Os servicos de Odontologia, Psicologia e Fisioterapia estao presentes em toda clinica
	all fil: Filial | one o: Odontologia | one p: Psicologia | one f: Fisioterapia |
	let ser = fil.servicos | o in ser and p in ser and f in ser
}


pred TodoServicoPertenceAUmaFilial {
	all s: Servico | some s.~servicos
}

pred TodoServicoTemApenasUmMedico{
	all ser: Servico | one ser.medico
} 

pred TodoAjudanteEstaParaUmServico{
	all ajud: Ajudante | some ajud.~ajudante

}

pred TodoMedicoTrabalhaEmAlgumServico {
	//todo medico faz parte do grupo de medicos de algum serviço da clinica
	all med: Medico | some med.~medico
}


pred TodoMedicoTemUmOuMaisPacientes{
	all med :Medico | some p :Paciente | p in med.pacientes
}

pred TodoPacienteEstaParaUmMedico{
	all pac: Paciente | some pac.~pacientes

}

---- Fatos ------

fact EstruturaDaClinica {
	TodoServicoTemApenasUmMedico
	TodaFilialPertenceAClinica
	TodaFilialTem3Servicos 
	TodoServicoPertenceAUmaFilial
	TodoMedicoTrabalhaEmAlgumServico
	TodoAjudanteEstaParaUmServico
	TodoPacienteEstaParaUmMedico

}

fact Quatidades{
	#Clinica = 1
	#Filial = 4
	#Medico.pacientes >=  && 	#Medico.pacientes <= 5
	//#Servico = 12 alternativa  predicado -> TodoServicoPertenceAUmaFilial
}



fact CadaServicoEstaParaUmaClinica{
	// Os servicos de Odontologia, Psicologia e Fisioterapia estao presentes em toda clinica e não pode estar simultaneamente em outra clinica
	all o: Odontologia, fil: Filial | (o in fil.servicos => (all fil2: Filial - fil | o !in fil2.servicos))
	all p: Psicologia, fil: Filial | (p in fil.servicos => (all fil2: Filial - fil | p !in fil2.servicos))
	all f: Fisioterapia, fil: Filial | (f in fil.servicos => (all fil2: Filial - fil | f !in fil2.servicos))	
}

fact CadaMedicoEstaParaUmServico {
	//Todo medico faz parte de um serviço e se um medico está em um serviço ele não pode estar em outro simultaneo
	all med: Medico , ser: Servico | (med in ser.medico => (all ser2: Servico  - ser | med !in ser2.medico))
} 

fact QuantidadeAjudantesPorEspecialidade{
	// Odontologia = 1
	all o: Odontologia | one o.ajudante
	//Psicologia = 0
	all p: Psicologia | no p.ajudante
	// Fisioterapia = 1 a 3
	all f: Fisioterapia | #ajudantesDeFisioterapia[f] >= 1 && #ajudantesDeFisioterapia[f] <= 3
}

fact CadaAjudanteEstaParaUmServico {
	//Todo ajudande faz parte de um serviço e se um ajudante está em um serviço ele não pode estar em outro simultaneo
	all ajud: Ajudante , ser: Servico | (ajud in ser.ajudante => (all ser2: Servico  - ser | ajud !in ser2.ajudante))
}

fact CadaPacienteEstaParaUmMedico {
	all pac: Paciente , med: Medico | (pac in med.pacientes => (all med2: Medico  - med | pac !in med2.pacientes))
}



------------------------------------ASSERTS------------------------------------



pred show[]{}
run show for 30

