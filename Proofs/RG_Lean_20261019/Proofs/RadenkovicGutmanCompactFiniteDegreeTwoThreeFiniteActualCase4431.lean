/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4431 : Family 9 := level9.get ⟨696,by decide⟩
def sourceMap4431 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,1,2,3,4,5,6] (sourceLabel 9 2 2 v)
def fusedMap4431 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4431_checked : acceptsGraphIso
    (source (graph core4431) (root 9) 2 2) DegreeTwoThreeSpectrum4958.graph sourceMap4431=true := by decide +kernel
theorem fusedMap4431_checked : acceptsGraphIso
    (fused (graph core4431) (root 9) 2 2) DegreeTwoThreeSpectrum4678.graph fusedMap4431=true := by decide +kernel
theorem certified4431 : Certified (graph core4431) (root 9) 2 2 :=
  of_native_maps core4431 DegreeTwoThreeSpectrum4958.graph DegreeTwoThreeSpectrum4678.graph
    sourceMap4431 fusedMap4431 sourceMap4431_checked fusedMap4431_checked
    DegreeTwoThreeFiniteComparisons.comparison4431
#print axioms sourceMap4431_checked
#print axioms fusedMap4431_checked
#print axioms certified4431
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
