/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4554 : Family 10 := level10.get ⟨461,by decide⟩
def sourceMap4554 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,10,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4554 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 2 2 v)
theorem sourceMap4554_checked : acceptsGraphIso
    (source (graph core4554) (root 10) 2 2) DegreeTwoThreeSpectrum6807.graph sourceMap4554=true := by decide +kernel
theorem fusedMap4554_checked : acceptsGraphIso
    (fused (graph core4554) (root 10) 2 2) DegreeTwoThreeSpectrum5900.graph fusedMap4554=true := by decide +kernel
theorem certified4554 : Certified (graph core4554) (root 10) 2 2 :=
  of_native_maps core4554 DegreeTwoThreeSpectrum6807.graph DegreeTwoThreeSpectrum5900.graph
    sourceMap4554 fusedMap4554 sourceMap4554_checked fusedMap4554_checked
    DegreeTwoThreeFiniteComparisons.comparison4554
#print axioms sourceMap4554_checked
#print axioms fusedMap4554_checked
#print axioms certified4554
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
