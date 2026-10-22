/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4305 : Family 9 := level9.get ⟨368,by decide⟩
def sourceMap4305 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4305 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4305_checked : acceptsGraphIso
    (source (graph core4305) (root 9) 2 2) DegreeTwoThreeSpectrum4737.graph sourceMap4305=true := by decide +kernel
theorem fusedMap4305_checked : acceptsGraphIso
    (fused (graph core4305) (root 9) 2 2) DegreeTwoThreeSpectrum4291.graph fusedMap4305=true := by decide +kernel
theorem certified4305 : Certified (graph core4305) (root 9) 2 2 :=
  of_native_maps core4305 DegreeTwoThreeSpectrum4737.graph DegreeTwoThreeSpectrum4291.graph
    sourceMap4305 fusedMap4305 sourceMap4305_checked fusedMap4305_checked
    DegreeTwoThreeFiniteComparisons.comparison4305
#print axioms sourceMap4305_checked
#print axioms fusedMap4305_checked
#print axioms certified4305
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
