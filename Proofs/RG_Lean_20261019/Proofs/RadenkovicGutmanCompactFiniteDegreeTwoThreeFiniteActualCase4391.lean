/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4391 : Family 9 := level9.get ⟨574,by decide⟩
def sourceMap4391 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,7,8,9,10,11,12] (sourceLabel 9 2 2 v)
def fusedMap4391 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4391_checked : acceptsGraphIso
    (source (graph core4391) (root 9) 2 2) DegreeTwoThreeSpectrum4918.graph sourceMap4391=true := by decide +kernel
theorem fusedMap4391_checked : acceptsGraphIso
    (fused (graph core4391) (root 9) 2 2) DegreeTwoThreeSpectrum4223.graph fusedMap4391=true := by decide +kernel
theorem certified4391 : Certified (graph core4391) (root 9) 2 2 :=
  of_native_maps core4391 DegreeTwoThreeSpectrum4918.graph DegreeTwoThreeSpectrum4223.graph
    sourceMap4391 fusedMap4391 sourceMap4391_checked fusedMap4391_checked
    DegreeTwoThreeFiniteComparisons.comparison4391
#print axioms sourceMap4391_checked
#print axioms fusedMap4391_checked
#print axioms certified4391
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
