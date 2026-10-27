/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4710 : Family 10 := level10.get ⟨906,by decide⟩
def sourceMap4710 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4710 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4710_checked : acceptsGraphIso
    (source (graph core4710) (root 10) 2 2) DegreeTwoThreeSpectrum7512.graph sourceMap4710=true := by decide +kernel
theorem fusedMap4710_checked : acceptsGraphIso
    (fused (graph core4710) (root 10) 2 2) DegreeTwoThreeSpectrum5772.graph fusedMap4710=true := by decide +kernel
theorem certified4710 : Certified (graph core4710) (root 10) 2 2 :=
  of_native_maps core4710 DegreeTwoThreeSpectrum7512.graph DegreeTwoThreeSpectrum5772.graph
    sourceMap4710 fusedMap4710 sourceMap4710_checked fusedMap4710_checked
    DegreeTwoThreeFiniteComparisons.comparison4710
#print axioms sourceMap4710_checked
#print axioms fusedMap4710_checked
#print axioms certified4710
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
