/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4395 : Family 9 := level9.get ⟨587,by decide⟩
def sourceMap4395 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4395 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4395_checked : acceptsGraphIso
    (source (graph core4395) (root 9) 2 2) DegreeTwoThreeSpectrum4922.graph sourceMap4395=true := by decide +kernel
theorem fusedMap4395_checked : acceptsGraphIso
    (fused (graph core4395) (root 9) 2 2) DegreeTwoThreeSpectrum4260.graph fusedMap4395=true := by decide +kernel
theorem certified4395 : Certified (graph core4395) (root 9) 2 2 :=
  of_native_maps core4395 DegreeTwoThreeSpectrum4922.graph DegreeTwoThreeSpectrum4260.graph
    sourceMap4395 fusedMap4395 sourceMap4395_checked fusedMap4395_checked
    DegreeTwoThreeFiniteComparisons.comparison4395
#print axioms sourceMap4395_checked
#print axioms fusedMap4395_checked
#print axioms certified4395
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
