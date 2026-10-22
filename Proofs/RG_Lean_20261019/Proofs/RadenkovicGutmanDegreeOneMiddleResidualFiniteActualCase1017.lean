/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1017 : Family 10 := level10.get ⟨935,by decide⟩
def sourceMap1017 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1017 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1017_checked : acceptsGraphIso
    (source (graph core1017) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2320.graph sourceMap1017=true := by decide +kernel
theorem fusedMap1017_checked : acceptsGraphIso
    (fused (graph core1017) (root 10) 2 2) DegreeTwoThreeSpectrum5831.graph fusedMap1017=true := by decide +kernel
theorem certified1017 : Certified (graph core1017) (root 10) 2 2 :=
  of_native_maps core1017 DegreeOneMiddleResidualSpectrum2320.graph DegreeTwoThreeSpectrum5831.graph
    sourceMap1017 fusedMap1017 sourceMap1017_checked fusedMap1017_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1017
#print axioms sourceMap1017_checked
#print axioms fusedMap1017_checked
#print axioms certified1017
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
