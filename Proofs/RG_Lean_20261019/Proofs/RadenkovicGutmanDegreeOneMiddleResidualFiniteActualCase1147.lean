/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1147 : Family 10 := level10.get ⟨1328,by decide⟩
def sourceMap1147 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1147 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1147_checked : acceptsGraphIso
    (source (graph core1147) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2211.graph sourceMap1147=true := by decide +kernel
theorem fusedMap1147_checked : acceptsGraphIso
    (fused (graph core1147) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1770.graph fusedMap1147=true := by decide +kernel
theorem certified1147 : Certified (graph core1147) (root 10) 2 2 :=
  of_native_maps core1147 DegreeOneMiddleResidualSpectrum2211.graph DegreeOneMiddleResidualSpectrum1770.graph
    sourceMap1147 fusedMap1147 sourceMap1147_checked fusedMap1147_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1147
#print axioms sourceMap1147_checked
#print axioms fusedMap1147_checked
#print axioms certified1147
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
