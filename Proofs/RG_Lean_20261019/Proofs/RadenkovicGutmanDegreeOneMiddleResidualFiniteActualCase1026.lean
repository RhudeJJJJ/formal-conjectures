/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1026 : Family 10 := level10.get ⟨995,by decide⟩
def sourceMap1026 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1026 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1026_checked : acceptsGraphIso
    (source (graph core1026) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1957.graph sourceMap1026=true := by decide +kernel
theorem fusedMap1026_checked : acceptsGraphIso
    (fused (graph core1026) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1509.graph fusedMap1026=true := by decide +kernel
theorem certified1026 : Certified (graph core1026) (root 10) 2 2 :=
  of_native_maps core1026 DegreeOneMiddleResidualSpectrum1957.graph DegreeOneMiddleResidualSpectrum1509.graph
    sourceMap1026 fusedMap1026 sourceMap1026_checked fusedMap1026_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1026
#print axioms sourceMap1026_checked
#print axioms fusedMap1026_checked
#print axioms certified1026
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
