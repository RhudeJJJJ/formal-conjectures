/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4704 : Family 10 := level10.get ⟨889,by decide⟩
def sourceMap4704 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4704 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4704_checked : acceptsGraphIso
    (source (graph core4704) (root 10) 2 2) DegreeTwoThreeSpectrum7511.graph sourceMap4704=true := by decide +kernel
theorem fusedMap4704_checked : acceptsGraphIso
    (fused (graph core4704) (root 10) 2 2) DegreeTwoThreeSpectrum5744.graph fusedMap4704=true := by decide +kernel
theorem certified4704 : Certified (graph core4704) (root 10) 2 2 :=
  of_native_maps core4704 DegreeTwoThreeSpectrum7511.graph DegreeTwoThreeSpectrum5744.graph
    sourceMap4704 fusedMap4704 sourceMap4704_checked fusedMap4704_checked
    DegreeTwoThreeFiniteComparisons.comparison4704
#print axioms sourceMap4704_checked
#print axioms fusedMap4704_checked
#print axioms certified4704
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
