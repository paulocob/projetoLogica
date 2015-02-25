module clinica/Cidade

// assinatura de Cidade vai mudar?
abstract sig Cidade { clinicas: set Clinicas }
one sig CampinaGrande, JoaoPessoa, Patos, SantaRita extends Cidade {}
