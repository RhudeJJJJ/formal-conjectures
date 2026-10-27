/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4325 : Family 9 := level9.get ⟨417,by decide⟩
def sourceMap4325 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4325 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4325_checked : acceptsGraphIso
    (source (graph core4325) (root 9) 2 2) DegreeTwoThreeSpectrum4791.graph sourceMap4325=true := by decide +kernel
theorem fusedMap4325_checked : acceptsGraphIso
    (fused (graph core4325) (root 9) 2 2) DegreeTwoThreeSpectrum4396.graph fusedMap4325=true := by decide +kernel
theorem certified4325 : Certified (graph core4325) (root 9) 2 2 :=
  of_native_maps core4325 DegreeTwoThreeSpectrum4791.graph DegreeTwoThreeSpectrum4396.graph
    sourceMap4325 fusedMap4325 sourceMap4325_checked fusedMap4325_checked
    DegreeTwoThreeFiniteComparisons.comparison4325
#print axioms sourceMap4325_checked
#print axioms fusedMap4325_checked
#print axioms certified4325
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
