/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1003 : Family 10 := level10.get ⟨897,by decide⟩
def sourceMap1003 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1003 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1003_checked : acceptsGraphIso
    (source (graph core1003) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2306.graph sourceMap1003=true := by decide +kernel
theorem fusedMap1003_checked : acceptsGraphIso
    (fused (graph core1003) (root 10) 2 2) DegreeTwoThreeSpectrum5762.graph fusedMap1003=true := by decide +kernel
theorem certified1003 : Certified (graph core1003) (root 10) 2 2 :=
  of_native_maps core1003 DegreeOneMiddleResidualSpectrum2306.graph DegreeTwoThreeSpectrum5762.graph
    sourceMap1003 fusedMap1003 sourceMap1003_checked fusedMap1003_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1003
#print axioms sourceMap1003_checked
#print axioms fusedMap1003_checked
#print axioms certified1003
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
