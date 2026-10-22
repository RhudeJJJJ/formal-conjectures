/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1128 : Family 10 := level10.get ⟨1272,by decide⟩
def sourceMap1128 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1128 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1128_checked : acceptsGraphIso
    (source (graph core1128) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2169.graph sourceMap1128=true := by decide +kernel
theorem fusedMap1128_checked : acceptsGraphIso
    (fused (graph core1128) (root 10) 2 2) DegreeTwoThreeSpectrum6536.graph fusedMap1128=true := by decide +kernel
theorem certified1128 : Certified (graph core1128) (root 10) 2 2 :=
  of_native_maps core1128 DegreeOneMiddleResidualSpectrum2169.graph DegreeTwoThreeSpectrum6536.graph
    sourceMap1128 fusedMap1128 sourceMap1128_checked fusedMap1128_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1128
#print axioms sourceMap1128_checked
#print axioms fusedMap1128_checked
#print axioms certified1128
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
