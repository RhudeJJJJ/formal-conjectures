/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4216 : Family 9 := level9.get ⟨109,by decide⟩
def sourceMap4216 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,10,11,12,13,14,15,9,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4216 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 2 2 v)
theorem sourceMap4216_checked : acceptsGraphIso
    (source (graph core4216) (root 9) 2 2) DegreeTwoThreeSpectrum4547.graph sourceMap4216=true := by decide +kernel
theorem fusedMap4216_checked : acceptsGraphIso
    (fused (graph core4216) (root 9) 2 2) DegreeTwoThreeSpectrum4110.graph fusedMap4216=true := by decide +kernel
theorem certified4216 : Certified (graph core4216) (root 9) 2 2 :=
  of_native_maps core4216 DegreeTwoThreeSpectrum4547.graph DegreeTwoThreeSpectrum4110.graph
    sourceMap4216 fusedMap4216 sourceMap4216_checked fusedMap4216_checked
    DegreeTwoThreeFiniteComparisons.comparison4216
#print axioms sourceMap4216_checked
#print axioms fusedMap4216_checked
#print axioms certified4216
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
