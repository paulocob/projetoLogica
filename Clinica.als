module clinica

----assinaturas---

one abstract sig Clinica { 
 localizacao: some Filial
}

abstract sig Filial {
	servicos: set Servico
}

abstract sig Servico {
	medico: some Medico
}

sig Odontologia, Psicologia, Fisioterapia extends Servico {}

sig Medico{
	ajudante: set Ajudante
}

one sig CampinaGrande, JoaoPessoa, Patos, SantaRita extends Filial {}

sig Ajudante{}

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


pred TodoMedicoTrabalhaEmAlgumServico {
	//todo medico faz parte do grupo de medicos de algum serviço da clinica
	all med: Medico | some med.~medico
}

pred TodoAjudanteEstaParaUmMedico {
	all ajud: Ajudante | some ajud.~ajudante

}

---- Fatos ------

fact EstruturaDaClinica {
	TodoServicoTemApenasUmMedico
	TodaFilialPertenceAClinica
	TodaFilialTem3Servicos 
	TodoServicoPertenceAUmaFilial
	TodoMedicoTrabalhaEmAlgumServico
	TodoAjudanteEstaParaUmMedico

}

fact Quatidades{
	#Clinica = 1
	#Filial = 4
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
	all o: Odontologia | one o.medico.ajudante
	//Psicologia = 0
	all p: Psicologia | no p.medico.ajudante
	// Fisioterapia = 1 a 3
	all f: Fisioterapia | ((one f.medico.ajudante) or	(#f.medico.ajudante = 2) or (#f.medico.ajudante = 3 ))
}

fact CadaAjudanteEstaParaUmServico {
	//Todo ajudande faz parte de um serviço e se um ajudante está em um serviço ele não pode estar em outro simultaneo
	all ajud: Ajudante , ser: Servico | (ajud in ser.medico.ajudante => (all ser2: Servico  - ser | ajud !in ser2.medico.ajudante))
}




pred show[]{}
run show for 20
