/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4285 : Family 9 := level9.get ⟨309,by decide⟩
def sourceMap4285 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,12,13,14,15,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 2 2 v)
def fusedMap4285 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4285_checked : acceptsGraphIso
    (source (graph core4285) (root 9) 2 2) DegreeTwoThreeSpectrum4765.graph sourceMap4285=true := by decide +kernel
theorem fusedMap4285_checked : acceptsGraphIso
    (fused (graph core4285) (root 9) 2 2) DegreeTwoThreeSpectrum4151.graph fusedMap4285=true := by decide +kernel
theorem certified4285 : Certified (graph core4285) (root 9) 2 2 :=
  of_native_maps core4285 DegreeTwoThreeSpectrum4765.graph DegreeTwoThreeSpectrum4151.graph
    sourceMap4285 fusedMap4285 sourceMap4285_checked fusedMap4285_checked
    DegreeTwoThreeFiniteComparisons.comparison4285
#print axioms sourceMap4285_checked
#print axioms fusedMap4285_checked
#print axioms certified4285
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
