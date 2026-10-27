/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4133 : Family 8 := level8.get ⟨126,by decide⟩
def sourceMap4133 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,13,14,7,8,9,10,11,12] (sourceLabel 8 2 2 v)
def fusedMap4133 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4133_checked : acceptsGraphIso
    (source (graph core4133) (root 8) 2 2) DegreeTwoThreeSpectrum3337.graph sourceMap4133=true := by decide +kernel
theorem fusedMap4133_checked : acceptsGraphIso
    (fused (graph core4133) (root 8) 2 2) DegreeTwoThreeSpectrum2588.graph fusedMap4133=true := by decide +kernel
theorem certified4133 : Certified (graph core4133) (root 8) 2 2 :=
  of_native_maps core4133 DegreeTwoThreeSpectrum3337.graph DegreeTwoThreeSpectrum2588.graph
    sourceMap4133 fusedMap4133 sourceMap4133_checked fusedMap4133_checked
    DegreeTwoThreeFiniteComparisons.comparison4133
#print axioms sourceMap4133_checked
#print axioms fusedMap4133_checked
#print axioms certified4133
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
