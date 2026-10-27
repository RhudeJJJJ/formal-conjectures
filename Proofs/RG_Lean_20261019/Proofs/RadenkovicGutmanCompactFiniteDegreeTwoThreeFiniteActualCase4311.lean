/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4311 : Family 9 := level9.get ⟨382,by decide⟩
def sourceMap4311 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap4311 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4311_checked : acceptsGraphIso
    (source (graph core4311) (root 9) 2 2) DegreeTwoThreeSpectrum4754.graph sourceMap4311=true := by decide +kernel
theorem fusedMap4311_checked : acceptsGraphIso
    (fused (graph core4311) (root 9) 2 2) DegreeTwoThreeSpectrum4321.graph fusedMap4311=true := by decide +kernel
theorem certified4311 : Certified (graph core4311) (root 9) 2 2 :=
  of_native_maps core4311 DegreeTwoThreeSpectrum4754.graph DegreeTwoThreeSpectrum4321.graph
    sourceMap4311 fusedMap4311 sourceMap4311_checked fusedMap4311_checked
    DegreeTwoThreeFiniteComparisons.comparison4311
#print axioms sourceMap4311_checked
#print axioms fusedMap4311_checked
#print axioms certified4311
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
