/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4333 : Family 9 := level9.get ⟨435,by decide⟩
def sourceMap4333 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,7,8,9,10,11,12] (sourceLabel 9 2 2 v)
def fusedMap4333 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4333_checked : acceptsGraphIso
    (source (graph core4333) (root 9) 2 2) DegreeTwoThreeSpectrum4811.graph sourceMap4333=true := by decide +kernel
theorem fusedMap4333_checked : acceptsGraphIso
    (fused (graph core4333) (root 9) 2 2) DegreeTwoThreeSpectrum4433.graph fusedMap4333=true := by decide +kernel
theorem certified4333 : Certified (graph core4333) (root 9) 2 2 :=
  of_native_maps core4333 DegreeTwoThreeSpectrum4811.graph DegreeTwoThreeSpectrum4433.graph
    sourceMap4333 fusedMap4333 sourceMap4333_checked fusedMap4333_checked
    DegreeTwoThreeFiniteComparisons.comparison4333
#print axioms sourceMap4333_checked
#print axioms fusedMap4333_checked
#print axioms certified4333
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
