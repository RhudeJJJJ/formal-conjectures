/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1005 : Family 10 := level10.get ⟨900,by decide⟩
def sourceMap1005 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1005 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1005_checked : acceptsGraphIso
    (source (graph core1005) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2308.graph sourceMap1005=true := by decide +kernel
theorem fusedMap1005_checked : acceptsGraphIso
    (fused (graph core1005) (root 10) 2 2) DegreeTwoThreeSpectrum5766.graph fusedMap1005=true := by decide +kernel
theorem certified1005 : Certified (graph core1005) (root 10) 2 2 :=
  of_native_maps core1005 DegreeOneMiddleResidualSpectrum2308.graph DegreeTwoThreeSpectrum5766.graph
    sourceMap1005 fusedMap1005 sourceMap1005_checked fusedMap1005_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1005
#print axioms sourceMap1005_checked
#print axioms fusedMap1005_checked
#print axioms certified1005
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
