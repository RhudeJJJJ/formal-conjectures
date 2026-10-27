/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4203 : Family 9 := level9.get ⟨59,by decide⟩
def sourceMap4203 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4203 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 2 2 v)
theorem sourceMap4203_checked : acceptsGraphIso
    (source (graph core4203) (root 9) 2 2) DegreeTwoThreeSpectrum4366.graph sourceMap4203=true := by decide +kernel
theorem fusedMap4203_checked : acceptsGraphIso
    (fused (graph core4203) (root 9) 2 2) DegreeTwoThreeSpectrum3958.graph fusedMap4203=true := by decide +kernel
theorem certified4203 : Certified (graph core4203) (root 9) 2 2 :=
  of_native_maps core4203 DegreeTwoThreeSpectrum4366.graph DegreeTwoThreeSpectrum3958.graph
    sourceMap4203 fusedMap4203 sourceMap4203_checked fusedMap4203_checked
    DegreeTwoThreeFiniteComparisons.comparison4203
#print axioms sourceMap4203_checked
#print axioms fusedMap4203_checked
#print axioms certified4203
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
