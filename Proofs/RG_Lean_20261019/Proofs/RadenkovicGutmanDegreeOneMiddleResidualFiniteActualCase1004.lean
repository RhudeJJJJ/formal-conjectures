/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1004 : Family 10 := level10.get ⟨898,by decide⟩
def sourceMap1004 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1004 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1004_checked : acceptsGraphIso
    (source (graph core1004) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2307.graph sourceMap1004=true := by decide +kernel
theorem fusedMap1004_checked : acceptsGraphIso
    (fused (graph core1004) (root 10) 2 2) DegreeTwoThreeSpectrum5763.graph fusedMap1004=true := by decide +kernel
theorem certified1004 : Certified (graph core1004) (root 10) 2 2 :=
  of_native_maps core1004 DegreeOneMiddleResidualSpectrum2307.graph DegreeTwoThreeSpectrum5763.graph
    sourceMap1004 fusedMap1004 sourceMap1004_checked fusedMap1004_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1004
#print axioms sourceMap1004_checked
#print axioms fusedMap1004_checked
#print axioms certified1004
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
