/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4389 : Family 9 := level9.get ⟨571,by decide⟩
def sourceMap4389 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4389 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4389_checked : acceptsGraphIso
    (source (graph core4389) (root 9) 2 2) DegreeTwoThreeSpectrum4916.graph sourceMap4389=true := by decide +kernel
theorem fusedMap4389_checked : acceptsGraphIso
    (fused (graph core4389) (root 9) 2 2) DegreeTwoThreeSpectrum4217.graph fusedMap4389=true := by decide +kernel
theorem certified4389 : Certified (graph core4389) (root 9) 2 2 :=
  of_native_maps core4389 DegreeTwoThreeSpectrum4916.graph DegreeTwoThreeSpectrum4217.graph
    sourceMap4389 fusedMap4389 sourceMap4389_checked fusedMap4389_checked
    DegreeTwoThreeFiniteComparisons.comparison4389
#print axioms sourceMap4389_checked
#print axioms fusedMap4389_checked
#print axioms certified4389
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
