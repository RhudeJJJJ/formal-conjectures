/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1160 : Family 10 := level10.get ⟨1407,by decide⟩
def sourceMap1160 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1160 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1160_checked : acceptsGraphIso
    (source (graph core1160) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2260.graph sourceMap1160=true := by decide +kernel
theorem fusedMap1160_checked : acceptsGraphIso
    (fused (graph core1160) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1834.graph fusedMap1160=true := by decide +kernel
theorem certified1160 : Certified (graph core1160) (root 10) 2 2 :=
  of_native_maps core1160 DegreeOneMiddleResidualSpectrum2260.graph DegreeOneMiddleResidualSpectrum1834.graph
    sourceMap1160 fusedMap1160 sourceMap1160_checked fusedMap1160_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1160
#print axioms sourceMap1160_checked
#print axioms fusedMap1160_checked
#print axioms certified1160
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
