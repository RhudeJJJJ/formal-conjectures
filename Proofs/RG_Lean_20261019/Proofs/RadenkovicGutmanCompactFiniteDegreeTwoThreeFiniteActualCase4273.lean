/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4273 : Family 9 := level9.get ⟨281,by decide⟩
def sourceMap4273 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,10,11,12,13,14,15,8,9,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4273 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4273_checked : acceptsGraphIso
    (source (graph core4273) (root 9) 2 2) DegreeTwoThreeSpectrum4879.graph sourceMap4273=true := by decide +kernel
theorem fusedMap4273_checked : acceptsGraphIso
    (fused (graph core4273) (root 9) 2 2) DegreeTwoThreeSpectrum4099.graph fusedMap4273=true := by decide +kernel
theorem certified4273 : Certified (graph core4273) (root 9) 2 2 :=
  of_native_maps core4273 DegreeTwoThreeSpectrum4879.graph DegreeTwoThreeSpectrum4099.graph
    sourceMap4273 fusedMap4273 sourceMap4273_checked fusedMap4273_checked
    DegreeTwoThreeFiniteComparisons.comparison4273
#print axioms sourceMap4273_checked
#print axioms fusedMap4273_checked
#print axioms certified4273
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
