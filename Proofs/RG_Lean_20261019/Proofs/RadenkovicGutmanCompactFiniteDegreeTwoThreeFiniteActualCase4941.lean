/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4941 : Family 10 := level10.get ⟨1463,by decide⟩
def sourceMap4941 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,10,11,12,13,14,15,16,7,8,9,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap4941 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4941_checked : acceptsGraphIso
    (source (graph core4941) (root 10) 2 2) DegreeTwoThreeSpectrum7495.graph sourceMap4941=true := by decide +kernel
theorem fusedMap4941_checked : acceptsGraphIso
    (fused (graph core4941) (root 10) 2 2) DegreeTwoThreeSpectrum6940.graph fusedMap4941=true := by decide +kernel
theorem certified4941 : Certified (graph core4941) (root 10) 2 2 :=
  of_native_maps core4941 DegreeTwoThreeSpectrum7495.graph DegreeTwoThreeSpectrum6940.graph
    sourceMap4941 fusedMap4941 sourceMap4941_checked fusedMap4941_checked
    DegreeTwoThreeFiniteComparisons.comparison4941
#print axioms sourceMap4941_checked
#print axioms fusedMap4941_checked
#print axioms certified4941
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
