module clinica

open util/ordering[Time]

----assinaturas---
sig Time {}

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

one sig CampinaGrande, JoaoPessoa /*Patos, SantaRita */extends Filial {}

sig Ajudante{}

sig Paciente{
	status: one StatusPaciente
}

abstract sig StatusPaciente {}

sig Consultado, EmConsulta, NaoConsultado extends StatusPaciente {}


	


----------------------------------- FUNCOES --------------------------------

fun ajudantesDeFisioterapia[ser : Servico]: set Ajudante{
	ser.ajudante		
}

fun getPacientes[med: Medico]: set Paciente{
	med.pacientes
}



--- predicado ---
//acho que isso fica no traces (Init)
pred TodaFilialPertenceAClinica {
	//Toda filial esta ligada a sua matriz
	all fil: Filial | some fil.~localizacao
}
//acho que isso fica no traces (Init)
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

pred TodoPacienteTemStatus{
	all pac : Paciente | some pac.~pacientes
}

pred TodoStatusEstaLigadoAUmPaciente{
	all stat: StatusPaciente | some stat.~status
	all stat: StatusPaciente , pac: Paciente | (stat in pac.status => (all pac2: Paciente  - pac | stat !in pac2.status))
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
	TodoStatusEstaLigadoAUmPaciente

}

fact Quatidades{
	#Clinica = 1
	#Filial = 2
	all med: Medico | #(getPacientes[med]) >=1 and #(getPacientes[med]) <= 5
	//#Medico.pacientes >= 1  and 	#Medico.pacientes <= 5
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
//acho que isso fica no traces (Init)
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
	all pac: Paciente , med: Medico | (pac in getPacientes[med] => (all med2: Medico  - med | pac !in getPacientes[med2]))
}



------------------------------------ASSERTS------------------------------------
assert todoServicoTemApenasUmMedico{
	all m:Medico | m in Servico.medico
}

assert todaFilialPertenceAClinica{
	all f:Filial | f in Clinica.localizacao
}

assert todoServicoFisioterapiaTemApenasUmAjudante{
	all f: Fisioterapia | #ajudantesDeFisioterapia[f] >= 1 && #ajudantesDeFisioterapia[f] <= 3
}

assert todoPacienteEstaAlocadoParaUmMedico{
	all p: Paciente | p in Medico.pacientes
}

assert todoServicoOdontologiaTemApenasUmAjudante{
	all o: Odontologia | #o.ajudante = 1
}

assert  todoServicoPsicologiaNaoPossuiAjudante{
	all p: Psicologia | #p.ajudante = 0
}

/*check todoServicoTemApenasUmMedico for 15
check  todaFilialPertenceAClinica for 15
check todoServicoFisioterapiaTemApenasUmAjudante for 15
check todoPacienteEstaAlocadoParaUmMedico for 15
check  todoServicoOdontologiaTemApenasUmAjudante for 15
check todoServicoPsicologiaNaoPossuiAjudante for 15*/





pred show[]{}
run show for 25
