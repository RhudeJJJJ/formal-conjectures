/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4620 : Family 10 := level10.get ⟨660,by decide⟩
def sourceMap4620 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,14,15,16,13,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4620 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4620_checked : acceptsGraphIso
    (source (graph core4620) (root 10) 2 2) DegreeTwoThreeSpectrum7318.graph sourceMap4620=true := by decide +kernel
theorem fusedMap4620_checked : acceptsGraphIso
    (fused (graph core4620) (root 10) 2 2) DegreeTwoThreeSpectrum5370.graph fusedMap4620=true := by decide +kernel
theorem certified4620 : Certified (graph core4620) (root 10) 2 2 :=
  of_native_maps core4620 DegreeTwoThreeSpectrum7318.graph DegreeTwoThreeSpectrum5370.graph
    sourceMap4620 fusedMap4620 sourceMap4620_checked fusedMap4620_checked
    DegreeTwoThreeFiniteComparisons.comparison4620
#print axioms sourceMap4620_checked
#print axioms fusedMap4620_checked
#print axioms certified4620
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
