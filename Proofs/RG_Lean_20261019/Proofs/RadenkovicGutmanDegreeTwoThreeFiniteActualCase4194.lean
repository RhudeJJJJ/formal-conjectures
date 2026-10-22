/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4194 : Family 9 := level9.get ⟨15,by decide⟩
def sourceMap4194 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4194 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (fusedLabel 9 2 2 v)
theorem sourceMap4194_checked : acceptsGraphIso
    (source (graph core4194) (root 9) 2 2) DegreeTwoThreeSpectrum4387.graph sourceMap4194=true := by decide +kernel
theorem fusedMap4194_checked : acceptsGraphIso
    (fused (graph core4194) (root 9) 2 2) DegreeTwoThreeSpectrum3860.graph fusedMap4194=true := by decide +kernel
theorem certified4194 : Certified (graph core4194) (root 9) 2 2 :=
  of_native_maps core4194 DegreeTwoThreeSpectrum4387.graph DegreeTwoThreeSpectrum3860.graph
    sourceMap4194 fusedMap4194 sourceMap4194_checked fusedMap4194_checked
    DegreeTwoThreeFiniteComparisons.comparison4194
#print axioms sourceMap4194_checked
#print axioms fusedMap4194_checked
#print axioms certified4194
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
