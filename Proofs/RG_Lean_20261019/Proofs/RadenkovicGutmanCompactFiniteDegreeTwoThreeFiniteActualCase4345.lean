/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4345 : Family 9 := level9.get ⟨467,by decide⟩
def sourceMap4345 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4345 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4345_checked : acceptsGraphIso
    (source (graph core4345) (root 9) 2 2) DegreeTwoThreeSpectrum4846.graph sourceMap4345=true := by decide +kernel
theorem fusedMap4345_checked : acceptsGraphIso
    (fused (graph core4345) (root 9) 2 2) DegreeTwoThreeSpectrum4498.graph fusedMap4345=true := by decide +kernel
theorem certified4345 : Certified (graph core4345) (root 9) 2 2 :=
  of_native_maps core4345 DegreeTwoThreeSpectrum4846.graph DegreeTwoThreeSpectrum4498.graph
    sourceMap4345 fusedMap4345 sourceMap4345_checked fusedMap4345_checked
    DegreeTwoThreeFiniteComparisons.comparison4345
#print axioms sourceMap4345_checked
#print axioms fusedMap4345_checked
#print axioms certified4345
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
