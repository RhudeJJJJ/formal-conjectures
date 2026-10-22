/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1131 : Family 10 := level10.get ⟨1276,by decide⟩
def sourceMap1131 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1131 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1131_checked : acceptsGraphIso
    (source (graph core1131) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2173.graph sourceMap1131=true := by decide +kernel
theorem fusedMap1131_checked : acceptsGraphIso
    (fused (graph core1131) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1734.graph fusedMap1131=true := by decide +kernel
theorem certified1131 : Certified (graph core1131) (root 10) 2 2 :=
  of_native_maps core1131 DegreeOneMiddleResidualSpectrum2173.graph DegreeOneMiddleResidualSpectrum1734.graph
    sourceMap1131 fusedMap1131 sourceMap1131_checked fusedMap1131_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1131
#print axioms sourceMap1131_checked
#print axioms fusedMap1131_checked
#print axioms certified1131
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
