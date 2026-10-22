/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4386 : Family 9 := level9.get ⟨566,by decide⟩
def sourceMap4386 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4386 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4386_checked : acceptsGraphIso
    (source (graph core4386) (root 9) 2 2) DegreeTwoThreeSpectrum4913.graph sourceMap4386=true := by decide +kernel
theorem fusedMap4386_checked : acceptsGraphIso
    (fused (graph core4386) (root 9) 2 2) DegreeTwoThreeSpectrum4209.graph fusedMap4386=true := by decide +kernel
theorem certified4386 : Certified (graph core4386) (root 9) 2 2 :=
  of_native_maps core4386 DegreeTwoThreeSpectrum4913.graph DegreeTwoThreeSpectrum4209.graph
    sourceMap4386 fusedMap4386 sourceMap4386_checked fusedMap4386_checked
    DegreeTwoThreeFiniteComparisons.comparison4386
#print axioms sourceMap4386_checked
#print axioms fusedMap4386_checked
#print axioms certified4386
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
