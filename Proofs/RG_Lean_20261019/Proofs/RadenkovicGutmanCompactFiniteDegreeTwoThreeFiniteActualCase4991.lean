/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4991 : Family 10 := level10.get ⟨1594,by decide⟩
def sourceMap4991 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4991 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4991_checked : acceptsGraphIso
    (source (graph core4991) (root 10) 2 2) DegreeTwoThreeSpectrum7592.graph sourceMap4991=true := by decide +kernel
theorem fusedMap4991_checked : acceptsGraphIso
    (fused (graph core4991) (root 10) 2 2) DegreeTwoThreeSpectrum6094.graph fusedMap4991=true := by decide +kernel
theorem certified4991 : Certified (graph core4991) (root 10) 2 2 :=
  of_native_maps core4991 DegreeTwoThreeSpectrum7592.graph DegreeTwoThreeSpectrum6094.graph
    sourceMap4991 fusedMap4991 sourceMap4991_checked fusedMap4991_checked
    DegreeTwoThreeFiniteComparisons.comparison4991
#print axioms sourceMap4991_checked
#print axioms fusedMap4991_checked
#print axioms certified4991
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
