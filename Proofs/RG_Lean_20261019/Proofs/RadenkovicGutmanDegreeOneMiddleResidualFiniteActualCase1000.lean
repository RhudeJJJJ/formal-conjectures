/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1000 : Family 10 := level10.get ⟨887,by decide⟩
def sourceMap1000 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1000 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1000_checked : acceptsGraphIso
    (source (graph core1000) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2303.graph sourceMap1000=true := by decide +kernel
theorem fusedMap1000_checked : acceptsGraphIso
    (fused (graph core1000) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1435.graph fusedMap1000=true := by decide +kernel
theorem certified1000 : Certified (graph core1000) (root 10) 2 2 :=
  of_native_maps core1000 DegreeOneMiddleResidualSpectrum2303.graph DegreeOneMiddleResidualSpectrum1435.graph
    sourceMap1000 fusedMap1000 sourceMap1000_checked fusedMap1000_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1000
#print axioms sourceMap1000_checked
#print axioms fusedMap1000_checked
#print axioms certified1000
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
