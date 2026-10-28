/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4985 : Family 10 := level10.get ⟨1584,by decide⟩
def sourceMap4985 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4985 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4985_checked : acceptsGraphIso
    (source (graph core4985) (root 10) 2 2) DegreeTwoThreeSpectrum7586.graph sourceMap4985=true := by decide +kernel
theorem fusedMap4985_checked : acceptsGraphIso
    (fused (graph core4985) (root 10) 2 2) DegreeTwoThreeSpectrum6073.graph fusedMap4985=true := by decide +kernel
theorem certified4985 : Certified (graph core4985) (root 10) 2 2 :=
  of_native_maps core4985 DegreeTwoThreeSpectrum7586.graph DegreeTwoThreeSpectrum6073.graph
    sourceMap4985 fusedMap4985 sourceMap4985_checked fusedMap4985_checked
    DegreeTwoThreeFiniteComparisons.comparison4985
#print axioms sourceMap4985_checked
#print axioms fusedMap4985_checked
#print axioms certified4985
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
