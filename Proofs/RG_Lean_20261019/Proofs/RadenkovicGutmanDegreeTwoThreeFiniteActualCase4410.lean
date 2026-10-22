/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4410 : Family 9 := level9.get ⟨618,by decide⟩
def sourceMap4410 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap4410 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4410_checked : acceptsGraphIso
    (source (graph core4410) (root 9) 2 2) DegreeTwoThreeSpectrum4937.graph sourceMap4410=true := by decide +kernel
theorem fusedMap4410_checked : acceptsGraphIso
    (fused (graph core4410) (root 9) 2 2) DegreeTwoThreeSpectrum4332.graph fusedMap4410=true := by decide +kernel
theorem certified4410 : Certified (graph core4410) (root 9) 2 2 :=
  of_native_maps core4410 DegreeTwoThreeSpectrum4937.graph DegreeTwoThreeSpectrum4332.graph
    sourceMap4410 fusedMap4410 sourceMap4410_checked fusedMap4410_checked
    DegreeTwoThreeFiniteComparisons.comparison4410
#print axioms sourceMap4410_checked
#print axioms fusedMap4410_checked
#print axioms certified4410
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
